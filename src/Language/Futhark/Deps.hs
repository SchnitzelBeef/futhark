{-# LANGUAGE ScopedTypeVariables #-}

-- | Finds dependencies between variables in programs
module Language.Futhark.Deps
  ( runDeps,
    testDeps,
    DepVal (..),
    BoundDepVal (..),
    NestedName (..),
    InnerDepVals,
    Env (..),
    Ids (..)
  )
where

import Data.Set qualified as S
import Control.Monad
import Data.Map qualified as M
import Language.Futhark
import Language.Futhark.FreeVars as FV
import Language.Futhark.Tuple as TPL
import Data.List.NonEmpty qualified as NE
import Data.List
import Data.Maybe (isJust)

type Error = String

newtype Ids = Ids [VName]
  deriving (Eq, Show)

type Deps = Ids

-- Data type for names in programs
data NestedName
  = Name VName
  | RecordName (M.Map Name NestedName)
  | WildcardName
  deriving (Eq, Show)

-- Core dependence data-type
data Struct = DepRecord | DepTuple 
  deriving (Eq, Show)

data DepVal
  = DepVal Deps
  | DepGroup Struct (M.Map Name DepVal)
  | DepFun DepsEnv [NestedName] (ExpBase Info VName) Deps
  deriving (Eq, Show)

data BoundDepVal
  = Depends VName DepVal
  | None (Maybe DepVal) -- In case we need BoundDepVal to act as a normal DepVal
  deriving (Eq, Show)

-- An environment mapping keys to values, 
newtype Env k a = Env (M.Map k a)
  deriving (Eq, Show)

type DepsEnv = Env VName DepVal

instance Semigroup DepsEnv where
  Env x <> Env y = Env $ x `M.union` y 

instance Monoid DepsEnv where
  mempty = Env $ M.empty

-- Alias for DepsEnv to make it easier to distinguish
type InnerDepVals = DepsEnv


-- Free monad definition
data Free e a
  = Pure a
  | Free (e (Free e a))

instance (Functor e) => Functor (Free e) where
  fmap f (Pure x) = Pure $ f x
  fmap f (Free g) = Free $ fmap (fmap f) g

instance (Functor e) => Applicative (Free e) where
  pure = Pure
  (<*>) = ap

instance (Functor e) => Monad (Free e) where
  Pure x >>= f = f x
  Free g >>= f = Free $ h <$> g
    where
      h x = x >>= f

-- The different operations the interpreter can do in a monadic context
data InterpretOp a
  = LogOp DepsEnv a
  | ReadOp (DepsEnv -> a)  
  | ErrorOp Error

instance Functor InterpretOp where
  fmap f (LogOp s x) = LogOp s $ f x
  fmap f (ReadOp k) = ReadOp $ f . k
  fmap _ (ErrorOp e) = ErrorOp e

-- Interpreter monad
type InterpretM a = Free InterpretOp a 

-- General environment functions
askEnv :: InterpretM DepsEnv
askEnv = Free $ ReadOp $ \env -> pure env

modifyEffects :: (Functor e, Functor h) => (e (Free e a) -> h (Free e a)) -> Free e a -> Free h a
modifyEffects _ (Pure x) = Pure x
modifyEffects g (Free e) = Free $ modifyEffects g <$> g e

localEnv :: (DepsEnv -> DepsEnv) -> InterpretM a -> InterpretM a
localEnv f = modifyEffects g
  where
    g (ReadOp k) = ReadOp $ k . f
    g op = op

failure :: String -> InterpretM a
failure = Free . ErrorOp

envSingle :: Maybe NestedName -> DepVal -> Either Error DepsEnv
envSingle names d = envExtend names d mempty

envSinglePure :: VName -> DepVal -> DepsEnv
envSinglePure vn d = Env $ M.singleton vn d

envExtend :: Maybe NestedName -> DepVal -> DepsEnv -> Either Error DepsEnv
envExtend (Just (Name vn)) d (Env env) = Right $ Env $ M.insert vn d env
envExtend (Just (RecordName r1)) (DepGroup _ r2) env
  | null r1 && null r2 = Right env
  | otherwise =
    let (names1, tpl1) = unzip $ TPL.sortFields r1
        (names2, tpl2) = unzip $ TPL.sortFields r2 
      in
        if names1 == names2
          then foldr envUnionError (Right env) $ map (\(x, y) -> envSingle (Just x) y) $ zip tpl1 tpl2
          else Left $ "Tried to extend environment non-matching records: " <>
                show r1 <> "\tand:\t" <> show r2
envExtend (Just (RecordName r)) d _ = Left $ 
      "Tried to extend environment with patterns of different dimensions: "
      ++ show r ++ "\tand:\t" ++ show d
envExtend (Just WildcardName) _ env = Right env
envExtend Nothing _ env = Right env

envExtendPure :: VName -> DepVal -> DepsEnv -> DepsEnv
envExtendPure vn d (Env env) = Env $ M.insert vn d env

envUnionError :: Either Error DepsEnv -> Either Error DepsEnv -> Either Error DepsEnv
envUnionError (Left e) _ = Left e
envUnionError  _ (Left e) = Left e
envUnionError (Right env1) (Right env2) = Right $ env1 <> env2

envLookup :: VName -> DepsEnv -> InterpretM DepVal
envLookup vn (Env env) = do
  -- If we know the variable, we return its dependencies. 
  -- Otherwise we return nothing (since it was not found with freeVars)
  -- This can happen in regards to type variables such as i32 or core Futhark functions such as map
  pure $
    case M.lookup vn env of
      Just x -> x
      Nothing -> DepVal mempty
      -- Alternatively: failure $ "Unknown variable: " <> (show vn) 
      -- Or: DepVal $ idsSingle vn

-- | Merges two lists of that have the order instance.
-- Used when combining two identifier sets which are always ordered
merge :: Ord a => [a] -> [a] -> [a]
merge [] [] = []
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
  | x < y  = x : merge xs (y:ys)
  | x > y  = y : merge (x:xs) ys
  | otherwise = x : merge xs ys

instance Semigroup DepVal where 
  (<>) = depValJoin

instance Monoid DepVal where 
  mempty = DepVal mempty


instance Semigroup Ids where
  Ids x <> Ids y = Ids $ merge x y

instance Monoid Ids where
  mempty = Ids mempty

idsSingle :: VName -> Ids
idsSingle v = Ids [v]

idsWithout :: VName -> Ids -> Ids
idsWithout x (Ids xs) = Ids $ filter (/=x) xs

-- | Extracting pure identifiers from DepVal
depValDeps :: DepVal -> Deps
depValDeps (DepVal x) = x
depValDeps (DepGroup _ x) = foldMap (depValDeps . snd) $ TPL.sortFields x
depValDeps (DepFun _ lst eb f_deps) =
  f_deps <> (foldr idsWithout (Ids $ freeVarsList eb) $ concat $ map nestedNameDeps lst)
  where nestedNameDeps :: NestedName -> [VName]
        nestedNameDeps (Name vn) = [vn]
        nestedNameDeps (RecordName x) = concat $ map (nestedNameDeps . snd) $ M.toList x
        nestedNameDeps WildcardName = mempty

-- | Joins two different sets of DepVal
-- Only records of equal length and fields can be joined without collapsing to pure DepVal Deps
depValJoin :: DepVal -> DepVal -> DepVal
depValJoin x@(DepGroup t r1) y@(DepGroup _ r2) =
  let (names1, tpl1) = unzip $ TPL.sortFields r1
      (names2, tpl2) = unzip $ TPL.sortFields r2
    in
      if names1 == names2 
        then DepGroup t $ M.fromList $ zip names1 $ zipWith depValJoin tpl1 tpl2
        else DepVal $ depValDeps x <> depValDeps y
depValJoin x y = DepVal $ depValDeps x <> depValDeps y

-- | Injects dependencies into expressions
depValInj :: Deps -> DepVal -> DepVal
depValInj x (DepVal y) = DepVal $ x <> y
depValInj x (DepGroup t r) = 
  let (names, tpl) = unzip $ TPL.sortFields r
    in DepGroup t $ M.fromList $ zip names $ map (depValInj x) tpl
depValInj x (DepFun env par body deps) = DepFun env par body (deps <> x) 
depValInj x v = DepVal $ x <> depValDeps v

-- | Locates free variables in the body of ProgBase
-- OBS: Only handles the last progDecs currently
depsFreeVarsInProgBase :: ProgBase Info VName -> DepsEnv
depsFreeVarsInProgBase base =
  case last $ progDecs base of 
    ValDec valbind -> depsFreeVarsInExpBase $ valBindBody valbind
    _ -> mempty -- Should not return mempty

-- | Dependencies in ExpBase 
depsFreeVarsInExpBase :: ExpBase Info VName -> DepsEnv
depsFreeVarsInExpBase eb = Env $ M.fromList $ map (\x -> (x, DepVal mempty)) $ freeVarsList eb

-- | ExpBase to list of free variables in the form of VName's
freeVarsList :: ExpBase Info VName -> [VName]
freeVarsList eb = S.toList $ FV.fvVars $ freeInExp eb

-- | Converts pattern bases to pure NestedNames ** UNFINISHED
extractPatBaseName :: PatBase Info VName t -> NestedName
extractPatBaseName (TuplePat pb_n _) = RecordName $ TPL.tupleFields $ map extractPatBaseName pb_n
extractPatBaseName (RecordPat npb_n _) = RecordName $ M.fromList $ map (\(L _ x, y) -> (x, extractPatBaseName y)) npb_n
extractPatBaseName (PatParens pb _) = extractPatBaseName pb
extractPatBaseName (Id vn _ _) = Name vn
extractPatBaseName (PatAscription pb _ _) = extractPatBaseName pb
extractPatBaseName _ = WildcardName
-- Missing: PatConst and PatAttr


-- | Converts nested names to pure DepsEnv's, should be used with care
nestedNamesToSelfEnv :: NestedName -> DepsEnv
nestedNamesToSelfEnv (Name vn) = Env $ M.singleton vn $ DepVal $ idsSingle vn
nestedNamesToSelfEnv (RecordName nv_n) = foldMap (nestedNamesToSelfEnv . snd) $ M.toList nv_n
nestedNamesToSelfEnv WildcardName = mempty

-- | Finds dependencies in declaration bases
depsDecBase :: DecBase Info VName -> InterpretM DepVal
depsDecBase (ValDec bindings) = do
  env <- askEnv
  let env' = foldMap (nestedNamesToSelfEnv . extractPatBaseName) $ valBindParams bindings
    in localEnv (const $ env' <> env) $ depsExpBase $ valBindBody bindings
    -- ^^ Above line should probably not be used since it may override definitions
depsDecBase (TypeDec _) = failure "Does not support analysis of TypeDec"
depsDecBase (ModTypeDec _) = failure "Does not support analysis of ModTypeDec"
depsDecBase (ModDec _) = failure "Does not support analysis of ModDec"
depsDecBase (OpenDec _ _) = failure "Does not support analysis of OpenDec"
depsDecBase (LocalDec db _) = depsDecBase db 
depsDecBase (ImportDec _ _ _) = failure "Does not support analysis of ImportDec"
-- ^ The above errors will not be thrown if evaluated using deps' for prettier printing

-- | Finds dependencies in expression bases
depsExpBase :: ExpBase Info VName -> InterpretM DepVal
depsExpBase (Literal _ _) = pure $ DepVal mempty
depsExpBase (IntLit _ _ _) = pure $ DepVal mempty
depsExpBase (FloatLit _ _ _) = pure $ DepVal mempty
depsExpBase (StringLit _ _) = pure $ DepVal mempty
depsExpBase (Hole _ _) = pure $ DepVal mempty
depsExpBase (Var qn _ _) = do
  env <- askEnv
  envLookup (qualLeaf qn) env
depsExpBase (Parens eb _) = depsExpBase eb
depsExpBase (QualParens qn eb _) = do
  env <- askEnv
  d1 <- envLookup (qualLeaf $ fst qn) env
  d2 <- depsExpBase eb
  pure $ d1 `depValJoin` d2
depsExpBase (TupLit ebn _) = do
  d_n <- mapM depsExpBase ebn
  pure $ DepGroup DepTuple $ TPL.tupleFields d_n
depsExpBase (RecordLit fb_n _) = do
  d_n <- mapM depsFieldBase fb_n
  pure $ DepGroup DepRecord $ M.fromList $ zip (map extractFieldBaseName fb_n) d_n
  where extractFieldBaseName :: FieldBase Info VName -> Name
        extractFieldBaseName (RecordFieldExplicit (L _ name) _ _) = name
        extractFieldBaseName (RecordFieldImplicit (L _ (VName name _)) _ _) = name
depsExpBase (ArrayLit eb_n _ _) = do
  d_n <- mapM depsExpBase eb_n
  pure $ foldr depValJoin mempty d_n
depsExpBase (ArrayVal _ _ _) = pure $ DepVal mempty
depsExpBase (Attr _ eb _) = depsExpBase eb 
depsExpBase (Project name eb _ _) = do
  d1 <- depsExpBase eb
  case d1 of
    (DepGroup _ r) ->
      let (names, tpl) = unzip $ TPL.sortFields r
          i = elemIndex name names
        in case i of
            (Just i') -> pure $ tpl !! i'
            Nothing -> failure $ "Projection of tuple/record out of bounds with name "
    _ -> failure "Tried to project a non-tuple/record"
depsExpBase (Negate eb _) = depsExpBase eb
depsExpBase (Not eb _) = depsExpBase eb
depsExpBase (Assert eb1 eb2 _ _) = do
  d1 <- depsExpBase eb1
  d2 <- depsExpBase eb2
  pure $ d1 <> d2
depsExpBase (Constr _ eb_n _ _) = do
  d_n <- mapM depsExpBase eb_n
  pure $ foldr depValJoin mempty d_n
depsExpBase (Update eb1 sb eb2 _) = do
  d1 <- depsExpBase eb1
  d2 <- depsExpBase eb2
  d_n <- depsSliceBase sb
  pure $ foldr depValJoin (d1 <> d2) d_n
depsExpBase (RecordUpdate eb1 n_n eb2 _ _) = do
  d1 <- depsExpBase eb1
  d2 <- depsExpBase eb2
  rcrdUpdate d1 d2 $ length n_n
  where rcrdUpdate :: DepVal -> DepVal -> Int -> InterpretM DepVal
        rcrdUpdate (DepGroup t rcrd) d' 1 | isJust $ M.lookup (head n_n) rcrd = do -- OBS use envLookup instead
          pure $ DepGroup t $ M.update (\_ -> Just d') (head n_n) rcrd
        rcrdUpdate (DepFun _ _ body f_deps) d' 1 = do
          d3 <- depsExpBase body
          rcrdUpdate (f_deps `depValInj` d3) d' 1 
          {- If the function has arguments, it becomes an AppExp containing a
            RecordUpdate instead, which is why this (^) is correct even though
            it seems odd. -}
        rcrdUpdate _ d' names = failure $ "Record update error: " <>
                                 (show d') <> "\ton fields\t" <> (show names)
depsExpBase (OpSection qn _ _) = do
  env <- askEnv
  envLookup (qualLeaf qn) env
depsExpBase (OpSectionLeft qn _ eb _ _ _) = do
  env <- askEnv
  d0 <- envLookup (qualLeaf qn) env
  d1 <- depsExpBase eb
  pure $ d0 <> d1
depsExpBase (OpSectionRight qn _ eb _ _ _) = do
  env <- askEnv
  d0 <- envLookup (qualLeaf qn) env
  d1 <- depsExpBase eb
  pure $ d0 `depValJoin` d1
depsExpBase (ProjectSection _ _ _) = pure $ DepVal mempty
depsExpBase (IndexSection sb _ _) = do
  d_n <- depsSliceBase sb
  pure $ foldr depValJoin mempty d_n
depsExpBase (Ascript eb _ _) = depsExpBase eb
depsExpBase (Coerce eb _ _ _) = depsExpBase eb 
depsExpBase (Lambda pb_n eb _ _ _) = do
  env <- askEnv
  let names = map extractPatBaseName pb_n
    in pure $ DepFun env names eb mempty
depsExpBase (AppExp aeb _) = depsAppExpBase aeb

-- | Finds dependencies in field bases
depsFieldBase :: FieldBase Info VName -> InterpretM DepVal
depsFieldBase (RecordFieldExplicit _ eb _) = depsExpBase eb
depsFieldBase (RecordFieldImplicit (L _ vn) _ _) = do
  env <- askEnv
  envLookup vn env

-- | Finds dependencies in application expression bases
depsAppExpBase :: AppExpBase Info VName -> InterpretM DepVal
depsAppExpBase (Apply eb lst _) = do
  d1 <- depsExpBase eb
  d_n <- mapM depsExpBase $ map snd $ NE.toList lst
  case d1 of 
    DepFun env' n_n body f_deps -> do
      fun_env <- case foldr envUnionError (Right env') $ zipWith envSingle (map Just n_n) d_n of
                  Left e -> failure e
                  Right e -> pure e 
      d2 <- localEnv (const fun_env) $ depsExpBase body
      pure $ f_deps `depValInj` d2 
    {- Meeting a function that it does not know, it is simply a conservative 
       estimate that it uses all the free variables inside the expression, which
       are uncovered through depValJoin  
      -}
    _ -> pure $ foldr depValJoin d1 d_n
depsAppExpBase (Range eb1 maybe_eb2 _ _) = do
  d1 <- depsExpBase eb1
  d2 <- maybe (pure $ DepVal mempty) depsExpBase maybe_eb2
  pure $ d1 `depValJoin` d2
depsAppExpBase (LetPat _ pb eb1 eb2 _) = do
  d1 <- depsExpBase eb1
  env <- askEnv
  let name = extractPatBaseName pb
    in do 
      logDep d1 name
      env' <- case envExtend (Just name) d1 env of
        (Left e) -> failure e
        (Right e) -> pure e
      localEnv (const env') $ depsExpBase eb2
depsAppExpBase (LetFun vn (_, pb_n, _, _, eb1) eb2 _ ) = do
  env <- askEnv
  let fun = DepFun env (map extractPatBaseName pb_n) eb1 mempty
    in do
      logDep (DepVal $ Ids $ freeVarsList eb1) $ Name vn
      env' <- pure $ envExtendPure vn fun env
      localEnv (const env') $ depsExpBase eb2
depsAppExpBase (If eb1 eb2 eb3 _) = do
  d1 <- depsExpBase eb1
  d2 <- depsExpBase eb2
  d3 <- depsExpBase eb3
  pure $ depValDeps d1 `depValInj` (d2 `depValJoin` d3)
depsAppExpBase (Loop _ pb lib lfb eb _) = 
  let vn = extractPatBaseName pb
    in do
      d1 <- case lib of
        (LoopInitExplicit eb') -> depsExpBase eb'
        (LoopInitImplicit (Info eb')) -> depsExpBase eb'
      env <- askEnv
      loop_env <- case envExtend (Just vn) d1 env of
        Right e -> pure e
        Left e -> failure e
      case lfb of
        For ib' eb' -> do
          d2 <- localEnv (const loop_env) $ depsExpBase eb'
          d3 <- loop vn (Just $ Name $ identName ib') d1
          pure $ depValDeps d2 `depValInj` d3
        ForIn pb' eb' ->
          let vn' = Just $ extractPatBaseName pb'
            in do
              d2 <- localEnv (const loop_env) $ depsExpBase eb'
              d3 <- loop vn vn' d1
              pure $ depValDeps d2 `depValInj` d3
        While eb' -> do
          d2 <- localEnv (const loop_env) $ depsExpBase eb'
          d3 <- loop vn Nothing d1
          pure $ depValDeps d2 `depValInj` d3
      where loop :: NestedName -> Maybe NestedName -> DepVal -> InterpretM DepVal
            loop p i ld = do
              env  <- askEnv
              env' <- case (envSingle i (DepVal mempty), envSingle (Just p) ld) of
                        (Left e, _) -> failure e
                        (_, Left e) -> failure e
                        (Right env1, Right env2) -> pure $ env2 <> env1 <> env
              ld' <- localEnv (const env') $ depsExpBase eb
              if ld == ld'
                then pure ld'
                else loop p i $ ld <> ld' 
depsAppExpBase (BinOp qn _ eb1 eb2 _) = do
  env <- askEnv
  d0 <- envLookup (qualLeaf $ fst qn) env
  d1 <- depsExpBase $ fst eb1
  d2 <- depsExpBase $ fst eb2
  pure $ d0 <> d1 <> d2
depsAppExpBase (LetWith ib1 ib2 sb eb1 eb2 _) = do
  d_n <- depsSliceBase sb
  d1 <- depsExpBase eb1
  -- We could log the new array that is created.
  -- It depends on all the values of the first expression base but also
  -- indirectly on all the dependencies of the consumed array
  env <- askEnv
  d2 <- envLookup (identName ib2) env
  logDep (d1 <> d2) $ Name $ identName ib1
  env' <- pure $ envExtendPure (identName ib1) d1 env
  inj_deps <- pure $ foldMap depValDeps d_n
  res <- localEnv (const env') $ depsExpBase eb2
  pure $ inj_deps `depValInj` res
depsAppExpBase (Index eb sb _) = do
  d <- depsExpBase eb 
  d_n <- depsSliceBase sb
  pure $ foldr depValJoin d d_n 
depsAppExpBase (Match eb ne_cb _) = do
  d1 <- depsExpBase eb
  d_n <- mapM depsCaseBase (NE.toList ne_cb)
  pure $ foldr depValJoin mempty $ map (\x -> depValInj (depValDeps x) d1) d_n
  -- OBS use of injection (might need to be removed)

depsSizeBinderList :: [SizeBinder VName] -> InterpretM DepVal
depsSizeBinderList sb_n = do
  env <- askEnv
  d_n <- mapM (\x -> envLookup (sizeName x) env) sb_n
  pure $ foldr depValJoin mempty d_n

-- | Finds dependencies in case bases
depsCaseBase :: CaseBase Info VName -> InterpretM DepVal
depsCaseBase (CasePat pb eb _) = do 
  d1 <- depsPatBase pb
  d2 <- depsExpBase eb
  pure $ depValDeps d1 `depValInj` d2 -- OBS use of injection here (might need to be removed)

-- | Finds dependencies in dimension index bases
depsDimIndexBase :: DimIndexBase Info VName -> InterpretM DepVal
depsDimIndexBase (DimFix eb) = depsExpBase eb
depsDimIndexBase (DimSlice maybe_eb1 maybe_eb2 maybe_eb3) = do
  d1 <- maybe (pure $ DepVal mempty) depsExpBase maybe_eb1
  d2 <- maybe (pure $ DepVal mempty) depsExpBase maybe_eb2
  d3 <- maybe (pure $ DepVal mempty) depsExpBase maybe_eb3
  pure $ d1 `depValJoin` d2 `depValJoin` d3

-- | Finds dependencies in pattern bases
-- Should maybe be removed as size can always be inferred
-- Yet it may still contain inner dependencies
depsPatBase :: PatBase Info VName t -> InterpretM DepVal
depsPatBase (TuplePat pb_n _) = do
  d_n <- mapM depsPatBase pb_n
  pure $ DepGroup DepTuple $ TPL.tupleFields d_n 
depsPatBase (RecordPat rcrd _) = do
  d_n <- mapM (depsPatBase . snd) rcrd
  pure $ foldr depValJoin mempty d_n
depsPatBase (PatParens pb _) = depsPatBase pb
depsPatBase (Id vn _ _) = pure $ DepVal $ Ids [vn]
depsPatBase (Wildcard _ _) = pure $ DepVal mempty
depsPatBase (PatAscription pb _ _) = depsPatBase pb
depsPatBase (PatLit _ _ _) = pure $ DepVal mempty
depsPatBase (PatConstr _ _ pb_n _) = do
  d_n <- mapM depsPatBase pb_n
  pure $ foldr depValJoin mempty d_n
depsPatBase (PatAttr _ pb _) = depsPatBase pb

-- | Finds dependencies in type argument expressions
depsTypeArgExp :: TypeArgExp (ExpBase Info VName) VName -> InterpretM DepVal
depsTypeArgExp (TypeArgExpSize se) = depsSizeExp se
depsTypeArgExp (TypeArgExpType _) = pure $ DepVal mempty

-- | Finds dependencies in size expressions
depsSizeExp :: SizeExp (ExpBase Info VName) -> InterpretM DepVal
depsSizeExp (SizeExp eb _) = depsExpBase eb
depsSizeExp (SizeExpAny _) = pure $ DepVal mempty

-- | Finds dependencies in slice bases
depsSliceBase :: SliceBase Info VName -> InterpretM [DepVal]
depsSliceBase = mapM depsDimIndexBase

-- | Recursive executer of evaluation
logDepsM :: DepsEnv -> InterpretM DepVal -> (Either Error DepVal, InnerDepVals)
logDepsM _ (Pure x) = (Right x, mempty)
logDepsM env (Free (ReadOp k)) = logDepsM env $ k env
logDepsM env (Free (LogOp d1 x)) =
  let (y, d2) = logDepsM env x
    in (y, d2 <> d1)
logDepsM _ (Free (ErrorOp e)) = (Left e, mempty)

-- | Logs dependencies
logDep :: DepVal -> NestedName -> InterpretM ()
logDep d (Name vn) = Free $ LogOp (envSinglePure vn d) $ pure () 
logDep (DepGroup _ r1) (RecordName r2) = do
  let (_, tpl1) = unzip $ TPL.sortFields r1 -- OBS does not check if names match
      (_, tpl2) = unzip $ TPL.sortFields r2
    in do
      _ <- zipWithM logDep tpl1 tpl2
      pure () 
logDep _ WildcardName = pure ()
logDep a b = failure $ "Failed to log an inner dependence between " <> show b <>
                         "\tand\t" <> show a 

-- Finds the relation between the name and the explicit ExpBase definition i a DecBase
bindingInDecBase :: DecBase Info VName -> BoundDepVal
bindingInDecBase (ValDec bind) = 
  let func = DepFun mempty (map extractPatBaseName $ valBindParams bind) (valBindBody bind) mempty
    in Depends (valBindName bind) func
bindingInDecBase (LocalDec db _) = bindingInDecBase db 
bindingInDecBase _ = None Nothing

-- | Interpretation function for dependencies
deps :: DepsEnv -> Prog -> [Either Error (BoundDepVal, InnerDepVals)]
deps env prog = 
  let bindings = map bindingInDecBase $ progDecs prog
      env' = foldMap joinBindings bindings -- A two pass scan*
        where joinBindings :: BoundDepVal -> DepsEnv
              joinBindings (Depends vn d) = envSinglePure vn d
              joinBindings _ = mempty 
  in map repack $ zip bindings $ map (logDepsM (env' <> env) . depsDecBase) $ progDecs prog
        where repack :: (BoundDepVal, (Either Error DepVal, InnerDepVals)) -> Either Error (BoundDepVal, InnerDepVals)
              repack (Depends vn _, (Right d2, d3)) = Right (Depends vn d2, d3)
              repack (None _, (Right d2, d3)) = Right (None (Just d2), d3)
              repack (Depends vn _, (Left e, _)) = Left $ "In function" ++ show vn ++ "\n" ++ e
              repack (None _, (Left e, _)) = Left e
-- *Turns out this is unnecessary since Futhark doesn't do support functions defined later in the program :-)  

joinDeps :: [Either Error (BoundDepVal, InnerDepVals)] -> DepsEnv
joinDeps [] = mempty
joinDeps (Right (Depends vn d, d_n):t) = envExtendPure vn d d_n <> joinDeps t
joinDeps (_:t) = joinDeps t

prettyPrinter :: Either Error (BoundDepVal, InnerDepVals) -> String -> String
prettyPrinter (Right (bound, Env d_n)) acc =
          "\n\ESC[0mFunction: \ESC[95m" ++ show bound ++
          "\n\ESC[0m\tInner dependencies: \ESC[36m" ++ 
          (foldr (\(k, a) x -> x ++ "\n\t\t" ++ show k ++ " depends on " ++ show a) "" $ M.toList d_n)
          ++ "\ESC[0m\n" ++ acc 
prettyPrinter (Left e) acc =
          "\n\ESC[31mError in dependency interpreter in function: \ESC[95m" ++ show e ++ acc


depsFolder :: forall a . ([Either Error (BoundDepVal, InnerDepVals)] -> a -> a) -> a -> [Prog] -> a
depsFolder printer base progs = 
  snd $ foldr depsFolder' (mempty, base) progs
        where depsFolder' :: Prog -> (DepsEnv, a) -> (DepsEnv, a) 
              depsFolder' p (env, s) =
                let either_d = deps (env <> depsFreeVarsInProgBase p) p
                  in (joinDeps either_d <> env, printer either_d s)
 
-- | Finds dependencies in a program
runDeps :: [Prog] -> String
runDeps progs = depsFolder (\d s -> foldr prettyPrinter s d) "" progs

-- | Tester function for dependencies
testDeps :: [Prog] -> [[Either Error (BoundDepVal, InnerDepVals)]]
testDeps progs = depsFolder (\d s -> [d] ++ s) [] progs

-- | Function for unit-testing specific parts of the ast
-- depsTestExp :: ExpBase Info VName -> Either Error (DepVal, DepsEnv) 
-- depsTestExp eb =
--   case logDepsM (depsFreeVarsInExpBase eb) $ depsExpBase eb of
--     (Left e, _) -> Left e 
--     (Right d, id_n) -> Right (d, id_n)
