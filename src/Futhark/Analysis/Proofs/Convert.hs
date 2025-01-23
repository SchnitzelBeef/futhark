module Futhark.Analysis.Proofs.Convert (mkIndexFnProg, mkIndexFnValBind) where

import Control.Applicative ((<|>))
import Control.Monad (foldM, foldM_, forM, forM_, unless, void, when, zipWithM_)
import Data.Bifunctor
import Data.Foldable (for_)
import Data.List qualified as L
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as M
import Data.Maybe (catMaybes, fromJust, fromMaybe, isJust, isNothing)
import Debug.Trace (traceM)
import Futhark.Analysis.Proofs.AlgebraBridge (addRelIterator, addRelSymbol, algebraContext, assume, paramToAlgebra, toAlgebra, ($==), ($>=))
import Futhark.Analysis.Proofs.AlgebraPC.Symbol qualified as Algebra
import Futhark.Analysis.Proofs.IndexFn (Cases (Cases), Domain (..), IndexFn (..), Iterator (..), cases, casesToList, catVar, flattenCases, getCase, justSingleCase)
import Futhark.Analysis.Proofs.IndexFnPlus (domainEnd, domainStart, intervalEnd, repCases, repIndexFn)
import Futhark.Analysis.Proofs.Monad
import Futhark.Analysis.Proofs.Query (Answer (..), Property (Injective, InjectiveOn), Query (..), askQ, askRefinement, askRefinements, foreachCase, isUnknown, isYes, prove)
import Futhark.Analysis.Proofs.Rewrite (rewrite, rewriteWithoutRules)
import Futhark.Analysis.Proofs.Substitute ((@))
import Futhark.Analysis.Proofs.Symbol (Symbol (..), neg, sop2Symbol)
import Futhark.Analysis.Proofs.Unify (Replacement, Substitution (mapping), mkRep, renamesM, rep, unify)
import Futhark.Analysis.Proofs.Util (prettyBinding, prettyBinding')
import Futhark.MonadFreshNames (VNameSource, newVName)
import Futhark.SoP.Monad (addProperty)
import Futhark.SoP.Refine (addRel)
import Futhark.SoP.SoP (Rel (..), SoP, int2SoP, justSym, mapSymSoP, negSoP, sym2SoP, (.+.), (.-.), (~*~), (~+~), (~-~))
import Futhark.Util.Pretty (prettyString)
import Language.Futhark qualified as E
import Language.Futhark.Semantic (FileModule (fileProg), ImportName, Imports)

--------------------------------------------------------------
-- Extracting information from E.Exp.
--------------------------------------------------------------
justVName :: E.Exp -> Maybe E.VName
justVName (E.Var (E.QualName [] vn) _ _) = Just vn
justVName _ = Nothing

getFun :: E.Exp -> Maybe String
getFun e = E.baseString <$> justVName e

getSize :: E.Exp -> IndexFnM (Maybe (SoP Symbol))
getSize (E.Var _ (E.Info {E.unInfo = (E.Scalar (E.Record _))}) loc) =
  errorMsg loc "Record-type variables must be unpacked."
getSize (E.Var _ (E.Info {E.unInfo = ty}) _) = sizeOfTypeBase ty
getSize (E.ArrayLit [] (E.Info {E.unInfo = ty}) _) = sizeOfTypeBase ty
getSize e = error $ "getSize: " <> prettyString e <> "\n" <> show e

sizeOfTypeBase :: E.TypeBase E.Size as -> IndexFnM (Maybe (SoP Symbol))
sizeOfTypeBase (E.Scalar (E.Refinement ty _)) =
  sizeOfTypeBase ty
sizeOfTypeBase (E.Scalar (E.Arrow _ _ _ _ return_type)) =
  sizeOfTypeBase (E.retType return_type)
sizeOfTypeBase (E.Array _ shape _)
  | dim : _ <- E.shapeDims shape = do
      -- FIXME Only supporting one dimensional arrays.
      ds <- forward dim
      case ds of
        [f_d]
          | Just d <- justSingleCase f_d ->
              pure $ Just d
        [_] ->
          -- FIXME Pretty sure all branches would have the same size?
          -- So could we just pick one?
          error "sizeOfTypBase on multiple case function"
        _ ->
          error "Currently only has support for one dimensional arrays."
sizeOfTypeBase (E.Scalar (E.Record _)) =
  error "Run E.patternMap first"
sizeOfTypeBase _ = pure Nothing

typeIsBool :: E.TypeBase E.Exp as -> Bool
typeIsBool (E.Scalar (E.Prim E.Bool)) = True
typeIsBool _ = False

-- Strip unused information.
getArgs :: NE.NonEmpty (a, E.Exp) -> [E.Exp]
getArgs = map (stripExp . snd) . NE.toList
  where
    stripExp x = fromMaybe x (E.stripExp x)

-- Like patternMap, but doesn't discard information about wildcards.
patternMapAligned :: E.Pat t -> [(Maybe E.VName, t)]
patternMapAligned = map f . patIdentsAligned
  where
    f (v, E.Info t) = (v, t)

    patIdentsAligned (E.Id v t _) = [(Just v, t)]
    patIdentsAligned (E.PatParens p _) = patIdentsAligned p
    patIdentsAligned (E.TuplePat pats _) = foldMap patIdentsAligned pats
    patIdentsAligned (E.RecordPat fs _) = foldMap (patIdentsAligned . snd) fs
    patIdentsAligned (E.Wildcard t _) = [(Nothing, t)]
    patIdentsAligned (E.PatAscription p _ _) = patIdentsAligned p
    patIdentsAligned (E.PatLit _ t _) = [(Nothing, t)]
    patIdentsAligned (E.PatConstr _ _ ps _) = foldMap patIdentsAligned ps
    patIdentsAligned (E.PatAttr _ p _) = patIdentsAligned p

--------------------------------------------------------------
-- Construct index function for source program
--------------------------------------------------------------
mkIndexFnProg :: VNameSource -> Imports -> M.Map E.VName [IndexFn]
mkIndexFnProg vns prog = snd $ runIndexFnM (mkIndexFnImports prog) vns

mkIndexFnImports :: [(ImportName, FileModule)] -> IndexFnM ()
mkIndexFnImports = mapM_ (mkIndexFnDecs . E.progDecs . fileProg . snd)

-- A program is a list of declarations (DecBase); functions are value bindings
-- (ValBind). Everything is in an AppExp.

mkIndexFnDecs :: [E.Dec] -> IndexFnM ()
mkIndexFnDecs [] = pure ()
mkIndexFnDecs (E.ValDec vb : rest) = do
  _ <- mkIndexFnValBind vb
  mkIndexFnDecs rest
mkIndexFnDecs (_ : ds) = mkIndexFnDecs ds

-- toplevel_indexfns
mkIndexFnValBind :: E.ValBind -> IndexFnM [IndexFn]
-- mkIndexFnValBind (E.ValBind _ vn _ _ _ _ _ _ _ _)
--   | and (zipWith (==) (E.baseString vn) "PROOF_") = do
--     debugM $ "Skipping proof: " <> prettyString vn
--     pure []
mkIndexFnValBind val@(E.ValBind _ vn ret _ _ params body _ _ _) = do
  clearAlgEnv
  whenDebug . traceM $ "\n\n==== mkIndexFnValBind:\n\n" <> prettyString val
  forM_ params addTypeRefinement
  forM_ params addBooleanNames
  forM_ params addSizeVariables
  debugPrintAlgEnv
  indexfns <- forward body >>= mapM rewrite >>= bindfn vn
  insertTopLevel vn (params, indexfns)
  -- _ <- algebraContext indexfn $ do
  --   whenDebug . traceM $ "Algebra context for indexfn:\n"
  --   debugPrintAlgEnv
  for_ ret (checkRefinement indexfns)
  pure indexfns
  where
    checkRefinement indexfns (E.TEParens te _) =
      checkRefinement indexfns te
    checkRefinement indexfns te@(E.TERefine _ (E.Lambda lam_params lam_body _ _ _) loc) = do
      debugM . warningString $
        "\ESC[93mChecking post-condition:\n" <> prettyStr te <> "\ESC[0m"
      let param_names = map fst $ mconcat $ map patternMapAligned lam_params
      forM_ (zip param_names indexfns) $ \(nm, fn) ->
        when (isJust nm) . void $ bindfn (fromJust nm) [fn]
      postconds <- forward lam_body >>= mapM rewrite
      debugM $
        "Post-conditions after substituting in results:\n  "
          <> prettyStr postconds
      answer <- askRefinements postconds
      case answer of
        Yes -> do
          debugM (E.baseString vn <> " ∎\n\n")
          pure ()
        Unknown ->
          errorMsg loc $ "Failed to show refinement: " <> prettyString te
    checkRefinement _ (E.TERefine _ _ loc) = do
      errorMsg loc "Only lambda post-conditions are currently supported."
    checkRefinement indexfns (E.TETuple tes _)
      | length indexfns == length tes = do
          zipWithM_ checkRefinement (map (: []) indexfns) tes
      | otherwise =
          undefined
    checkRefinement _ _ = pure ()

bindfn :: E.VName -> [IndexFn] -> IndexFnM [IndexFn]
bindfn vn indexfn = do
  insertIndexFn vn indexfn
  whenDebug (traceM $ prettyBinding vn indexfn <> "\n")
  -- tell ["resulting in", toLaTeX (vn, indexfn')]
  pure indexfn

singleCase :: a -> Cases Symbol a
singleCase e = cases [(Bool True, e)]

fromScalar :: SoP Symbol -> [IndexFn]
fromScalar e = [IndexFn Empty (singleCase e)]

forward :: E.Exp -> IndexFnM [IndexFn]
forward (E.Parens e _) = forward e
forward (E.Attr _ e _) = forward e
forward (E.AppExp (E.LetPat _ (E.Id vn _ _) x in_body _) _) = do
  -- tell [textbf "Forward on " <> Math.math (toLaTeX vn) <> toLaTeX x]
  whenDebug . traceM $ "Forward on " <> prettyString vn
  (bindfn vn =<< forward x) >> forward in_body
forward (E.AppExp (E.LetPat _ (E.TuplePat patterns _) x body _) _) = do
  -- tell [textbf "Forward on " <> Math.math (toLaTeX (S.toList $ E.patNames p)) <> toLaTeX x]
  whenDebug . traceM $ "Forward on " <> prettyString patterns
  xs <- forward x
  forM_ (zip (mconcat $ map patternMapAligned patterns) xs) bindfnOrDiscard
  forward body
  where
    bindfnOrDiscard ((Nothing, _), _) = pure ()
    bindfnOrDiscard ((Just vn, _), indexfn) = void (bindfn vn [indexfn])
forward (E.Literal (E.BoolValue x) _) =
  pure . fromScalar . sym2SoP $ Bool x
forward (E.Literal (E.SignedValue (E.Int64Value x)) _) =
  pure . fromScalar . int2SoP $ toInteger x
forward (E.IntLit x _ _) =
  pure . fromScalar $ int2SoP x
forward (E.Negate x _) = do
  -- Numeric negation.
  fns <- forward x
  forM fns $ \fn -> do
    pure $
      IndexFn
        { iterator = iterator fn,
          body = cases [(p, negSoP v) | (p, v) <- casesToList (body fn)]
        }
forward e@(E.Var (E.QualName _ vn) _ _) = do
  bindings <- getIndexFns
  case M.lookup vn bindings of
    Just indexfns -> do
      pure indexfns
    _ -> do
      size <- getSize e
      case size of
        Just sz -> do
          -- Canonical array representation.
          i <- newVName "i"
          pure
            [ IndexFn
                { iterator = Forall i (Iota sz),
                  body = singleCase . sym2SoP $ Idx (Var vn) (sym2SoP $ Var i)
                }
            ]
        Nothing ->
          -- Canonical scalar representation.
          pure [IndexFn Empty (singleCase . sym2SoP $ Var vn)]
forward (E.TupLit xs _) = do
  mconcat <$> mapM forward xs
forward (E.AppExp (E.Index e_xs slice loc) _)
  | [E.DimFix e_idx] <- slice = do
      xss <- forward e_xs
      idxs <- forward e_idx
      forM (zip xss idxs) $ \(f_xs, f_idx) -> do
        -- If xs has a Cat iterator, we need to express k in terms of idx
        -- lest we capture k.
        k_rep <-
          case (iterator f_xs, justSingleCase f_idx) of
            (Forall _ (Cat k m b), Just idx) -> do
              s1 <- solve_for k b idx
              s2 <- solve_for k (intervalEnd $ Cat k m b) idx
              case s1 <|> s2 of
                Just s -> pure $ mkRep k s
                Nothing -> error "E.Index: Indexing would capture k"
            (Forall _ (Cat {}), Nothing) ->
              error "E.Index: Not implemented yet"
            _ ->
              pure mempty
        unless (null k_rep) $ debugPrettyM "E.Index: solved for k:" k_rep
        checkBounds f_xs f_idx k_rep
        i <- newVName "i"
        x <- newVName "x"
        let y =
              IndexFn
                { iterator = iterator f_idx,
                  body = singleCase . sym2SoP $ Idx (Var x) (sym2SoP $ Var i)
                }
        debugT' "E.Index result: " $
          substParams y [(i, f_idx), (x, repIndexFn k_rep f_xs)]
  where
    -- Solve for k in x(k) = y.
    solve_for k x y = do
      k_hole <- newVName "k_hole"
      let x_holed = rep (M.singleton k $ sym2SoP (Hole k_hole)) x
      s :: Maybe (Replacement Symbol) <- fmap mapping <$> unify x_holed y
      pure $ s >>= (M.!? k_hole)

    checkBounds (IndexFn Empty _) _ _ =
      error "E.Index: Indexing into scalar"
    checkBounds f_xs@(IndexFn (Forall _ dom) _) f_idx k_rep = algebraContext f_idx $ do
      dom_start <- rewrite $ domainStart dom
      dom_end <- rewrite $ domainEnd dom
      case dom of
        Cat k m _ | k `M.member` k_rep -> do
          let k_value = k_rep M.! k
          doCheck (\_ -> int2SoP 0 :<= k_value)
          doCheck (\_ -> k_value :<= m)
        Cat _ _ b -> do
          doCheck (\idx -> b :<= idx :|| dom_start :<= idx)
          doCheck (\idx -> idx :<= intervalEnd dom :|| idx :<= dom_end)
        Iota _ -> do
          doCheck (dom_start :<=)
          doCheck (:<= dom_end)
      where
        doCheck :: (SoP Symbol -> Symbol) -> IndexFnM ()
        doCheck bound =
          foreachCase f_idx $ \n -> do
            c <- askQ (CaseCheck bound) f_idx n
            let (p_idx, e_idx) = getCase n $ body f_idx
            unless (isYes c) $ do
              debugM $
                "Failed bounds-checking:"
                  <> "\nf_xs:"
                  <> prettyString f_xs
                  <> "\nf_idx: "
                  <> prettyString f_idx
                  <> "\nCASE f_idx: "
                  <> show n
              debugPrintAlgEnv
              errorMsg loc $
                "Unsafe indexing: "
                  <> showE e_idx
                  <> " (failed to show: "
                  <> prettyString p_idx
                  <> " => "
                  <> prettyString (bound e_idx)
                  <> ")."

    showE idx
      | Just vn <- justVName e_xs =
          prettyString $ Idx (Var vn) idx
    showE idx =
      "_[" <> prettyString idx <> "]"
forward (E.Not e _) = do
  fns <- forward e
  forM fns $ \fn -> do
    rewrite $
      IndexFn (iterator fn) $
        cmapValues (mapSymSoP (sym2SoP . neg)) (body fn)
forward (E.AppExp (E.BinOp (op', _) _ (x', _) (y', _) _) _)
  | E.baseTag (E.qualLeaf op') <= E.maxIntrinsicTag,
    name <- E.baseString $ E.qualLeaf op',
    Just bop <- L.find ((name ==) . prettyString) [minBound .. maxBound :: E.BinOp] = do
      vxs <- forward x'
      vys <- forward y'
      forM (zip vxs vys) $ \(vx, vy) -> do
        a <- newVName "a"
        b <- newVName "b"
        let doOp op =
              substParams
                (IndexFn Empty (singleCase $ op (Var a) (Var b)))
                [(a, vx), (b, vy)]
        case bop of
          E.Plus -> doOp (~+~)
          E.Times -> doOp (~*~)
          E.Minus -> doOp (~-~)
          E.Equal -> doOp (~==~)
          E.NotEqual -> doOp (~/=~)
          E.Less -> doOp (~<~)
          E.Greater -> doOp (~>~)
          E.Leq -> doOp (~<=~)
          E.Geq -> doOp (~>=~)
          E.LogAnd -> doOp (~&&~)
          E.LogOr -> doOp (~||~)
          _ -> error ("forward not implemented for bin op: " <> show bop)
forward (E.AppExp (E.If e_c e_t e_f _) _) = do
  cs <- forward e_c
  let f_c = case cs of
        [v] -> v
        _ -> error "If on tuple?"
  unless (iterator f_c == Empty) $ error "Condition in if-statement is an array?"
  cond <- newVName "if-condition"
  t_branch <- newVName "t_branch"
  f_branch <- newVName "f_branch"
  fn_if <-
    IndexFn
      (iterator f_c)
      ( cases
          [ (Var cond, sym2SoP $ Var t_branch),
            (neg $ Var cond, sym2SoP $ Var f_branch)
          ]
      )
      @ (cond, f_c)
  (ts, fs) <- algebraContext fn_if $ do
    ts <- rollbackAlgEnv $ do
      assume (getPredicate 0 fn_if)
      forward e_t
    fs <- rollbackAlgEnv $ do
      assume (getPredicate 1 fn_if)
      forward e_f
    pure (ts, fs)
  forM (zip ts fs) $ \(t, f) -> do
    substParams fn_if [(t_branch, t), (f_branch, f)]
  where
    getPredicate n fn = fst . getCase n $ body fn
forward (E.Lambda _ _ _ _ loc) =
  errorMsg loc "Cannot create index function for unapplied lambda."
forward expr@(E.AppExp (E.Apply f args loc) _)
  | Just fname <- getFun f,
    "map" `L.isPrefixOf` fname,
    E.Lambda params lam_body _ _ _ : _args <- getArgs args,
    Just arrays <- NE.nonEmpty (NE.tail args) = do
      (aligned_args, _aligned_sizes) <- zipArgs loc params arrays
      iter <- bindLambdaBodyParams (mconcat aligned_args)
      fns <- quantifiedBy iter $ forward lam_body

      forM fns $ \body_fn ->
        if iterator body_fn == Empty
          then rewrite $ IndexFn iter (body body_fn)
          else error "scan: Non-scalar body."
  | Just fname <- getFun f,
    "map" `L.isPrefixOf` fname = do
      -- No need to handle map non-lambda yet as program can just be rewritten.
      etaExpandErrorMsg loc (head $ getArgs args)
  | Just "replicate" <- getFun f,
    [n, x] <- getArgs args = do
      ns <- forward n
      xs <- forward x
      forM (zip ns xs) $ \(n', x') -> do
        i <- newVName "i"
        case (n', x') of
          ( IndexFn Empty (Cases ((Bool True, m) NE.:| [])),
            IndexFn Empty body
            ) ->
              -- XXX support only 1D arrays for now.
              rewrite $ IndexFn (Forall i (Iota m)) body
          _ -> undefined -- TODO See iota comment.
  | Just "iota" <- getFun f,
    [n] <- getArgs args = do
      ns <- forward n
      forM ns $ \n' -> do
        i <- newVName "i"
        case n' of
          IndexFn Empty (Cases ((Bool True, m) NE.:| [])) ->
            rewrite $ IndexFn (Forall i (Iota m)) (singleCase . sym2SoP $ Var i)
          _ -> undefined -- TODO We've no way to express this yet.
          -- Have talked with Cosmin about an "outer if" before.
  | Just fname <- getFun f,
    "zip" `L.isPrefixOf` fname = do
      mconcat <$> mapM forward (getArgs args)
  | Just fname <- getFun f,
    "unzip" `L.isPrefixOf` fname,
    [xs'] <- getArgs args =
      -- XXX unzip is a no-op.
      forward xs'
  | Just "scan" <- getFun f,
    [E.OpSection (E.QualName [] vn) _ _, _ne, xs'] <- getArgs args = do
      -- Scan with basic operator.
      fns <- forward xs'
      forM fns $ \fn -> do
        let i = case iterator fn of
              (Forall i' _) -> i'
              Empty -> error "scan array is empty?"
        -- TODO should we verify that _ne matches op?
        op <-
          case E.baseString vn of
            "+" -> pure (~+~)
            "-" -> pure (~-~)
            "*" -> pure (~*~)
            "&&" -> pure (~&&~)
            _ -> error ("scan not implemented for bin op: " <> show vn)
        let base_case = sym2SoP (Var i) :== int2SoP 0
        x <- newVName "a"
        let y =
              IndexFn
                (iterator fn)
                ( cases
                    [ (base_case, sym2SoP (Idx (Var x) (sVar i))),
                      (neg base_case, Recurrence `op` Idx (Var x) (sVar i))
                    ]
                )
        -- tell ["Using scan rule ", toLaTeX y]
        y @ (x, fn)
          >>= rewrite
  | Just "scan" <- getFun f,
    [E.Lambda params lam_body _ _ _, _ne, _xs] <- getArgs args,
    xs <- NE.fromList [NE.last args],
    [pat_acc, pat_x] <- params = do
      -- We pick the first argument of the lambda to be the accumulator
      -- and the second argument to be an element of the input array.
      -- (The lambda is associative, so we are free to pick.)
      (aligned_args, _) <- zipArgs loc [pat_x] xs
      iter <- bindLambdaBodyParams (mconcat aligned_args)
      let accToRec = M.fromList (map (,sym2SoP Recurrence) $ E.patNames pat_acc)
      fns <-
        quantifiedBy iter $
          map (repIndexFn accToRec) <$> forward lam_body

      forM fns $ \body_fn ->
        if iterator body_fn == Empty
          then rewrite $ IndexFn iter (body body_fn)
          else error "scan: Non-scalar body."
  | Just "scatter" <- getFun f,
    [dest_arg, inds_arg, vals_arg] <- getArgs args = do
      -- Scatter in-bounds-monotonic indices.
      --
      -- y = scatter dest inds vals
      -- where
      --   inds = ∀k ∈ [0, ..., m-1] .
      --       | seg(k+1) - seg(k) > 0  => seg(k)
      --       | seg(k+1) - seg(k) <= 0 => OOB
      --   seg(0) is 0
      --   seg(k) is monotonically increasing
      --   dest has size seg(m) - 1         (to ensure conclusion covers all of dest)
      --   OOB < 0 or OOB >= seg(m) - 1
      -- ___________________________________________________
      -- y = ∀i ∈ ⊎k=iota m [seg(k), ..., seg(k+1) - 1] .
      --     | i == inds[k] => vals[k]
      --     | i /= inds[k] => dest[i]
      --
      -- by the semantics of scatter, equivalent to
      -- y = ∀i ∈ ⊎k=iota m [seg(k), ..., seg(k+1) - 1] .
      --     | i == seg(k) => vals[k]
      --     | i /= seg(k) => dest[i]
      --
      -- (i == seg(k) implies seg(k+1) - seg(k) > 0, since otherwise
      --  the interval [seg(k), ..., seg(k+1) - 1] is empty and i could
      --  not be equal to seg(k).)
      -- TODO find a nicer way to express this index function.
      --
      --
      -- From type checking, we have:
      -- scatter : (dest : [n]t) -> (inds : [m]i64) -> (vals : [m]t) : [n]t
      -- \* inds and vals are same size
      -- \* dest and result are same size

      ----------------------------
      -- WIP More general rule:
      --
      --   inds = ∀k ∈ [0, ..., m-1] .
      --       | p(k) => seg(k)
      --       | p(k) => OOB
      --   seg(0) is 0
      --   seg(k) is monotonically increasing
      --   dest has size seg(m) - 1         (to ensure conclusion covers all of dest)
      --   OOB < 0 or OOB >= seg(m) - 1
      -- ___________________________________________________
      -- y = ∀i ∈ ⊎k=iota m [seg(k), ..., seg(k+1) - 1] .
      --     | i == inds[k] => vals[k]
      --     | i /= inds[k] => dest[i]
      -- y = ∀i ∈ ⊎k=iota m [seg(k), ..., seg(k+1) - 1] .
      --     | i == seg(k) ^ p(k) => vals[k]
      --     | i == OOB ^ not p(k) => vals[k]
      --     | i /= seg(k) ^ p(k) => dest[i]
      --     | i /= OOB ^ not p(k) => dest[i]
      --
      -- by OOB < 0, we know that i == OOB is false and i /= OOB is true:
      -- y = ∀i ∈ ⊎k=iota m [seg(k), ..., seg(k+1) - 1] .
      --     | i == seg(k) ^ p(k) => vals[k]
      --     | False ^ not p(k) => vals[k]
      --     | i /= seg(k) ^ p(k) => dest[i]
      --     | True ^ not p(k) => dest[i]
      --
      -- y = ∀i ∈ ⊎k=iota m [seg(k), ..., seg(k+1) - 1] .
      --     | i == seg(k) ^ p(k) => vals[k]
      --     | i /= seg(k) ^ p(k) => dest[i]
      --     | not p(k) => dest[i]
      --
      -- y = ∀i ∈ ⊎k=iota m [seg(k), ..., seg(k+1) - 1] .
      --     | i == seg(k) ^ p(k) => vals[k]
      --     | i /= seg(k) ^ p(k) || True ^ not p(k) => dest[i]
      --
      -- y = ∀i ∈ ⊎k=iota m [seg(k), ..., seg(k+1) - 1] .
      --     | i == seg(k) ^ p(k) => vals[k]
      --     | i /= seg(k) => dest[i]
      dests <- forward dest_arg >>= mapM rewrite
      indss <- forward inds_arg >>= mapM rewrite
      valss <- forward vals_arg >>= mapM rewrite
      forM (zip3 dests indss valss) $ \(dest, inds, vals) -> do
        -- 1. Check that inds is on the right form.
        vn_k <- newVName "k"
        vn_m <- newVName "m"
        vn_p0 <- newVName "p0"
        vn_f0 <- newVName "f0"
        vn_p1 <- newVName "p1"
        vn_f1 <- newVName "f1"
        let inds_template =
              IndexFn
                { iterator = Forall vn_k (Iota $ sym2SoP $ Hole vn_m),
                  body =
                    cases
                      [ (Hole vn_p0, sym2SoP $ Hole vn_f0),
                        (Hole vn_p1, sym2SoP $ Hole vn_f1)
                      ]
                }
        s <- fromMaybe (error "unhandled scatter") <$> unify inds_template inds
        -- Safe to do this now:
        let IndexFn inds_iter@(Forall k (Iota m)) _ = inds
        -- Determine which is OOB and which is e1.
        let isOOB ub = CaseCheck (\c -> c :< int2SoP 0 :|| (mapping s M.! ub) :<= c)
        (vn_p_seg, vn_f_seg) <- do
          case0_is_OOB <- askQ (isOOB vn_f1) inds 0
          case case0_is_OOB of
            Yes -> pure (vn_p1, vn_f1)
            Unknown -> do
              case1_is_OOB <- askQ (isOOB vn_f0) inds 1
              case case1_is_OOB of
                Yes -> pure (vn_p0, vn_f0)
                Unknown -> error "scatter: unable to determine OOB branch"
        let p_seg = sop2Symbol $ mapping s M.! vn_p_seg
        let f_seg = mapping s M.! vn_f_seg
        -- Check that p_seg = f_seg(k+1) - f_seg(k) > 0.
        algebraContext inds $ do
          addRelIterator inds_iter
          seg_delta <- rewrite $ rep (mkRep k (sVar k .+. int2SoP 1)) f_seg .-. f_seg
          p_desired_form :: Maybe (Substitution Symbol) <- unify p_seg (seg_delta :> int2SoP 0)
          unless (isJust p_desired_form) $ error "scatter: p is not on desired form"
        -- Check that seg(0) = 0.
        -- (Not using CaseCheck as it has to hold outside case predicate.)
        let x `at_k` i = rep (mkRep k i) x
        let zero :: SoP Symbol = int2SoP 0
        eq0 <- f_seg `at_k` zero $== int2SoP 0
        when (isUnknown eq0) $ error "scatter: unable to determine segment start"
        -- Check that seg is monotonically increasing. (Essentially checking
        -- that OOB branch is never taken in inds.)
        algebraContext inds $ do
          addRelIterator inds_iter
          seg_delta <- rewrite $ rep (mkRep k (sVar k .+. int2SoP 1)) f_seg .-. f_seg
          mono <- seg_delta $>= int2SoP 0
          when (isUnknown mono) $ error "scatter: unable to show segment monotonicity"
        -- Check that the proposed end of segments seg(m) - 1 equals the size of dest.
        -- (Note that has to hold outside the context of inds, so we cannot assume p_seg.)
        let IndexFn (Forall _ dom_dest) _ = dest
        let dest_size = domainEnd dom_dest
        domain_covered <- f_seg `at_k` m .-. int2SoP 1 $== dest_size
        when (isUnknown domain_covered) $
          error "scatter: segments do not cover iterator domain"
        i <- newVName "i"
        dest_hole <- newVName "dest_hole"
        vals_hole <- newVName "vals_hole"
        let p = sVar i :== f_seg
        let fn =
              IndexFn
                { iterator = Forall i (Cat k m f_seg),
                  body =
                    cases
                      [ (p, sym2SoP $ Apply (Var vals_hole) [sVar k]),
                        (neg p, sym2SoP $ Apply (Var dest_hole) [sVar i])
                      ]
                }
        substParams fn [(vals_hole, vals), (dest_hole, dest)]
  | Just "sized" <- getFun f,
    [_, e] <- getArgs args = do
      -- No-op.
      forward e
  | Just "injective" <- getFun f,
    [e_xs] <- getArgs args = do
      xss <- forward e_xs
      forM xss $ \xs -> do
        fromPreludeEffect loc expr xs $ prove Injective xs
  | Just "injectiveOn" <- getFun f,
    [e_rng, e_xs] <- getArgs args = do
      rng <- forward e_rng
      case rng of
        [IndexFn Empty cs_start, IndexFn Empty cs_end] -> do
          xss <- forward e_xs
          let start = flattenCases cs_start
          let end = flattenCases cs_end
          forM xss $ \xs -> do
            fromPreludeEffect loc expr xs $ prove (InjectiveOn start end) xs
        _ -> undefined
  | Just "and" <- getFun f,
    [e_xs] <- getArgs args = do
      -- No-op: The argument e_xs is a boolean array; each branch will
      -- be checked in refinements.
      -- XXX but we lose information about iterator at check site, hm...
      xss <- forward e_xs
      forM xss $ \xs -> do
        -- It's easier to do check here than after converting xss into
        -- a reduce.
        fromPreludeEffect loc expr xs $ askRefinement xs
  -- _ -> do
  --   emitWarning
  --   let Forall _ dom = iterator xs -- e_xs is array type.
  --   let n = domainEnd dom
  --   j <- newVName "j"
  --   vn <- newVName "and_xs"
  --   let summation = Sum j (int2SoP 0) n (Idx (Var vn) (sym2SoP $ Var j))
  --   IndexFn
  --     { iterator = Empty,
  --       body = cases [(Bool True, sym2SoP $ n :== sym2SoP summation)]
  --     }
  --     @ (vn, xs)
  --   where
  --     emitWarning =
  --       warningMsg loc $
  --         "Failed to simplify: "
  --           <> prettyString expr
  --           <> "\nIndex function:\n"
  --           <> prettyString xs
  -- Applying other functions, for instance, user-defined ones.
  | (E.Var (E.QualName [] g) info loc') <- f,
    E.Scalar (E.Arrow _ _ _ _ (E.RetType _ return_type)) <- E.unInfo info = do
      toplevel <- getTopLevelIndexFns
      case M.lookup g toplevel of
        Just (pats, indexfns) -> do
          forM indexfns $ \indexfn -> do
            whenDebug . traceM $ "✨ Using index fn " <> prettyBinding' g indexfn
            (actual_args, actual_sizes) <- zipArgs loc' pats args

            let size_rep = M.fromList $ mconcat actual_sizes
            whenDebug . traceM $
              "Size variable replacement " <> prettyString size_rep

            -- Check that preconditions are satisfied.
            foldM_
              ( \args_in_scope (pat, arg) -> do
                  let scope = args_in_scope <> arg
                  checkPatPrecondition size_rep scope pat
                  pure scope
              )
              []
              (zip pats actual_args)
            -- The resulting index fn will be fully applied, so we can rewrite recurrences here.
            -- (Which speeds up things by eliminating cases.)
            debugT' "Result: " $
              substParams (repIndexFn size_rep indexfn) (mconcat actual_args)
                >>= rewrite
          where
            checkPatPrecondition size_rep scope pat = do
              cond <- getPrecondition pat
              ans <- case cond of
                Nothing -> pure Yes
                Just check -> do
                  whenDebug . traceM $
                    "Checking precondition " <> prettyString pat <> " for " <> prettyString g
                  check (size_rep, scope)
              unless (isYes ans) . errorMsg loc $
                "Failed to show precondition " <> prettyString pat <> " in context: " <> prettyString scope
        Nothing -> do
          -- g is a free variable in this expression (probably a parameter
          -- to the top-level function currently being analyzed).
          arg_fns <- mconcat <$> mapM forward (getArgs args)
          size <- sizeOfTypeBase return_type
          arg_names <- forM arg_fns (const $ newVName "x")
          iter <- case size of
            Just sz ->
              flip Forall (Iota sz) <$> newVName "i"
            Nothing ->
              pure Empty
          let g_fn =
                IndexFn
                  { iterator = iter,
                    body =
                      singleCase . sym2SoP $
                        Apply (Var g) (map (sym2SoP . Var) arg_names)
                  }
          when (typeIsBool return_type) $ addProperty (Algebra.Var g) Algebra.Boolean
          fn <- substParams g_fn (zip arg_names arg_fns)
          pure [fn]
forward e = error $ "forward on " <> show e <> "\nPretty: " <> prettyString e

-- Align parameters and arguments. Each parameter is a pattern.
-- A pattern unpacks to a list of (optional) names with type information.
-- An argument is an expression, which `forward` will, correspondingly,
-- return a list of index functions for.
-- Patterns and arguments must align---otherwise an error is raised.
zipArgs ::
  E.SrcLoc ->
  [E.Pat E.ParamType] ->
  NE.NonEmpty (a, E.Exp) ->
  IndexFnM ([[(E.VName, IndexFn)]], [[(E.VName, SoP Symbol)]])
zipArgs loc formal_args actual_args = do
  let pats = map patternMapAligned formal_args
  args <- mapM forward (getArgs actual_args)

  unless (length pats == length args) $
    errorMsg loc "Functions must be fully applied. Maybe you want to eta-expand?"
  unless (map length pats == map length args) $
    errorMsg loc "Internal error: actual argument does not match parameter pattern."

  -- Discard unused parameters such as wildcards while maintaining alignment.
  let aligned_args = do
        (pat, arg) <- zip pats args
        pure . catMaybes $ zipWith (\vn fn -> (,fn) <$> vn) (map fst pat) arg

  -- When applying bound functions size parameters must be replaced as well.
  -- (E.g., if we are zipping index functions with use of a top-level definition.)
  aligned_sizes <- forM (zip pats args) $ \(pat, arg) -> do
    let types = map snd pat
    size_names <- mapM (fmap (>>= getVName) . sizeOfTypeBase) types
    arg_sizes <- mapM sizeOfDomain arg
    -- Assert that if there is a size parameter, then we have a size to bind it to.
    when (any (\(vn, sz) -> isJust vn && isNothing sz) (zip size_names arg_sizes)) $
      errorMsg loc "Internal error: sizes don't align."
    pure $ catMaybes $ zipMaybes size_names arg_sizes

  pure (aligned_args, aligned_sizes)
  where
    getVName x | Just (Var vn) <- justSym x = Just vn
    getVName _ = Nothing

    sizeOfDomain (IndexFn Empty _) = pure Nothing
    sizeOfDomain (IndexFn (Forall _ d) _) =
      Just <$> rewrite (domainEnd d .-. domainStart d .+. int2SoP 1)

    zipMaybes = zipWith (liftA2 (,))

substParams :: (Foldable t) => IndexFn -> t (E.VName, IndexFn) -> IndexFnM IndexFn
substParams = foldM substParam
  where
    -- We want to simplify, but avoid rewriting recurrences during
    -- paramter-substitution.
    substParam fn (paramName, paramIndexFn) =
      (fn @ (paramName, paramIndexFn)) >>= rewriteWithoutRules

cmap :: ((a, b) -> (c, d)) -> Cases a b -> Cases c d
cmap f (Cases xs) = Cases (fmap f xs)

cmapValues :: (b -> c) -> Cases a b -> Cases a c
cmapValues f = cmap (second f)

sVar :: E.VName -> SoP Symbol
sVar = sym2SoP . Var

-- TODO eh bad
(~==~) :: Symbol -> Symbol -> SoP Symbol
x ~==~ y = sym2SoP $ sym2SoP x :== sym2SoP y

(~/=~) :: Symbol -> Symbol -> SoP Symbol
x ~/=~ y = sym2SoP $ sym2SoP x :/= sym2SoP y

(~<~) :: Symbol -> Symbol -> SoP Symbol
x ~<~ y = sym2SoP $ sym2SoP x :< sym2SoP y

(~>~) :: Symbol -> Symbol -> SoP Symbol
x ~>~ y = sym2SoP $ sym2SoP x :> sym2SoP y

(~<=~) :: Symbol -> Symbol -> SoP Symbol
x ~<=~ y = sym2SoP $ sym2SoP x :<= sym2SoP y

(~>=~) :: Symbol -> Symbol -> SoP Symbol
x ~>=~ y = sym2SoP $ sym2SoP x :>= sym2SoP y

(~&&~) :: Symbol -> Symbol -> SoP Symbol
x ~&&~ y = sym2SoP $ x :&& y

(~||~) :: Symbol -> Symbol -> SoP Symbol
x ~||~ y = sym2SoP $ x :|| y

--------------------------------------------------------------
-- Handling refinement types.
--------------------------------------------------------------
type CheckContext = (Replacement Symbol, [(E.VName, IndexFn)])

type Check = CheckContext -> IndexFnM Answer

type Effect = IndexFnM ()

getPrecondition :: E.PatBase E.Info E.VName (E.TypeBase dim u) -> IndexFnM (Maybe Check)
getPrecondition = fmap (fmap fst) . getRefinement

getRefinement :: E.PatBase E.Info E.VName (E.TypeBase dim u) -> IndexFnM (Maybe (Check, Effect))
getRefinement (E.PatParens pat _) = getRefinement pat
getRefinement (E.PatAscription pat _ _) = getRefinement pat
getRefinement (E.Id param (E.Info {E.unInfo = info}) _loc)
  | E.Array _ _ (E.Refinement _ty ref) <- info = do
      whenDebug . traceM $ "Getting (array) type refinement " <> prettyString (param, ref)
      hole <- sym2SoP . Hole <$> newVName "h"
      Just <$> mkRef ((`Idx` hole) . Var) ref
  | E.Scalar (E.Refinement _ty ref) <- info = do
      whenDebug . traceM $ "Getting type refinement " <> prettyString (param, ref)
      Just <$> mkRef Var ref
  where
    mkRef wrap (E.OpSectionRight (E.QualName [] vn_op) _ e_y _ _ _) = do
      let rel = case E.baseString vn_op of
            ">" -> (:>)
            ">=" -> (:>=)
            "<" -> (:<)
            "<=" -> (:<=)
            "==" -> (:==)
            "!=" -> (:/=)
            _ -> undefined
      ys <- forwardRefinementExp e_y
      debugPrintAlgEnv
      -- Create check as an index function whose cases contain the refinement.
      let check =
            mkCheck $
              IndexFn Empty . cases $
                map (second (sym2SoP . (sym2SoP (Var param) `rel`))) (casesToList ys)
      let effect = do
            -- (We allow Holes in wrap and toAlgebra cannot be called on symbols with Holes.)
            alg_vn <- paramToAlgebra param wrap
            y <- rewrite $ flattenCases ys
            addRelSymbol $ sym2SoP (Var alg_vn) `rel` y
      pure (check, effect)
    mkRef wrap (E.Lambda lam_params lam_body _ _ _) = do
      let param_names = map fst $ mconcat $ map patternMapAligned lam_params
      case param_names of
        [lam_param] -> do
          body <- forwardRefinementExp lam_body
          let ref = case lam_param of
                Just vn -> repCases (mkRep vn $ wrap param) body
                Nothing -> body
          let check = mkCheck $ IndexFn Empty ref
          let effect = do
                y <- rewrite $ flattenCases ref
                addRelSymbol (sop2Symbol y)
          pure (check, effect)
        _ ->
          error "Impossible: Refinements have type t -> bool."
    mkRef _ x = error $ "Unhandled refinement predicate " <> show x

    forwardRefinementExp e = do
      fns <- forward e
      case fns of
        [fn] -> body <$> rewrite fn
        _ -> error "Impossible: Refinements have return type bool."

    -- Check that all branches of check_fn evaluate to true
    -- when substituting in param_subst.
    mkCheck check_fn (size_rep, args_in_scope) = do
      -- Substitute parameters in scope.
      -- The refinement of a parameter can use previous parameters:
      --   (x : []i64) (n : {i64 | (== sum x))
      -- NOTE unpacked record-types are disallowed:
      --   (x : {(t1, t2) | \(a, b) -> ...})
      check <- substParams (repIndexFn size_rep check_fn) args_in_scope
      askRefinement check
getRefinement _ = pure Nothing

-- This function adds the effects of type refinements to the environment
-- without checking that they hold.
-- Use this function on the parameters of top-level definitions, where
-- refinements are pre-requisites assumed to be true.
addTypeRefinement :: E.PatBase E.Info E.VName E.ParamType -> IndexFnM ()
addTypeRefinement pat = do
  ref <- getRefinement pat
  case ref of
    Just (_, effect) -> effect
    _ -> pure ()

addBooleanNames :: E.PatBase E.Info E.VName E.ParamType -> IndexFnM ()
addBooleanNames (E.PatParens pat _) = addBooleanNames pat
addBooleanNames (E.PatAscription pat _ _) = addBooleanNames pat
addBooleanNames (E.Id param (E.Info {E.unInfo = E.Array _ _ t}) _) = do
  when (typeIsBool $ E.Scalar t) $ addProperty (Algebra.Var param) Algebra.Boolean
addBooleanNames (E.Id param (E.Info {E.unInfo = t}) _) = do
  when (typeIsBool t) $ addProperty (Algebra.Var param) Algebra.Boolean
addBooleanNames _ = pure ()

-- Lowerbounds size variables by 0.
addSizeVariables :: E.PatBase E.Info E.VName E.ParamType -> IndexFnM ()
addSizeVariables (E.PatParens pat _) = addSizeVariables pat
addSizeVariables (E.PatAscription pat _ _) = addSizeVariables pat
addSizeVariables (E.Id _ (E.Info {E.unInfo = E.Array _ shp _}) _) = do
  mapM_ addSize (E.shapeDims shp)
  where
    addSize (E.Var (E.QualName _ d) _ _) = do
      alg_d <- toAlgebra (sym2SoP $ Var d)
      addRel (alg_d :>=: int2SoP 0)
    addSize _ = pure ()
addSizeVariables (E.Id param (E.Info {E.unInfo = t}) _) = do
  when (typeIsBool t) $ addProperty (Algebra.Var param) Algebra.Boolean
addSizeVariables _ = pure ()

-- Binds names of scalar parameters to scalar values of corresponding
-- index functions. Assumes that domains are equivalent across index
-- functions. Returns the most "complex" iterator over these domains.
-- For example, this would transform the lambda body of the following
--   map (\x y z -> x + y + z) xs ys zs
-- into
--   map (\i -> xs[i] + ys[i] + zs[i]) (indices xs)
-- where xs is the index function with the most "complex" iterator.
bindLambdaBodyParams :: [(E.VName, IndexFn)] -> IndexFnM Iterator
bindLambdaBodyParams params = do
  -- Make sure all Cat k bound in iterators are identical by renaming.
  fns <- renamesM (map snd params)
  let iter@(Forall i _) = maximum (map iterator fns)
  forM_ (zip (map fst params) fns) $ \(paramName, fn) -> do
    vn <- newVName "tmp_fn"
    IndexFn tmp_iter cs <-
      IndexFn iter (singleCase . sym2SoP $ Idx (Var vn) (sVar i)) @ (vn, fn)
    -- Renaming k bound in `tmp_iter` to k bound in `iter`.
    let k_rep =
          fromMaybe mempty $ mkRep <$> catVar tmp_iter <*> (sVar <$> catVar iter)
    insertIndexFn paramName [repIndexFn k_rep $ IndexFn Empty cs]
  pure iter

errorMsg :: E.SrcLoc -> String -> a
errorMsg loc msg =
  error $
    "Error at " <> prettyString (E.locText (E.srclocOf loc)) <> ": " <> msg

etaExpandErrorMsg :: E.SrcLoc -> E.Exp -> a
etaExpandErrorMsg loc fn =
  errorMsg loc $
    "Only anonymous functions may be passed as argument. Perhaps you want to eta-expand: "
      <> prettyString fn

warningMsg :: (Applicative f, E.Located a) => a -> String -> f ()
warningMsg loc msg = do
  traceM . warningString $
    prettyString (E.locText (E.srclocOf loc)) <> ": " <> msg

quantifiedBy :: Iterator -> IndexFnM a -> IndexFnM a
quantifiedBy Empty m = m
quantifiedBy iter m =
  rollbackAlgEnv $ do
    addRelIterator iter
    m

fromPreludeEffect :: (Monad m, E.Located a1, Pretty a2, Pretty a3) => a1 -> a2 -> a3 -> m Answer -> m IndexFn
fromPreludeEffect loc expr fn m = do
  ans <- m
  case ans of
    Yes ->
      pure $ IndexFn Empty (cases [(Bool True, int2SoP 1)])
    _ ->
      errorMsg loc $
        "Failed to show: "
          <> prettyString expr
          <> "\nIndex function:\n"
          <> prettyString fn
