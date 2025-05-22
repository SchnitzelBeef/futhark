-- | Finds dependencies between variables in programs
module Language.Futhark.Deps
  ( deps,
    depsTestExp,
    DepVal (..),
    InnerDepVal (..),
    NestedVName (..),
    Ids (..)
  )
where

import Data.Set qualified as S
import Control.Monad
import Data.Map qualified as M
import Language.Futhark
import Language.Futhark.FreeVars as FV
import Data.List.NonEmpty qualified as NE
import Text.Read

type Error = String

newtype Ids = Ids [VName]
  deriving (Eq, Show)

type Deps = Ids

data DepVal
  = DepVal Ids
  | DepTuple [DepVal]
  | DepFun DepsEnv [NestedVName] (ExpBase Info VName)
  deriving (Eq, Show)

data InnerDepVal = Depends NestedVName DepVal
  deriving (Eq, Show)

type DepsEnv = M.Map VName DepVal

data NestedVName
  = Name VName
  | Tuple [NestedVName]
  | WildcardName
  deriving (Eq, Show)
{-  
    Could add a "lambdaParam [NestedVName] instance for functions,
    but this would only be for internal purposes.
    Right now this is fixed by having DepFun take a list of NestedVName
    which are the parameters of a function
-}

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

data EvalOp a
  = LogOp InnerDepVal a
  | ReadOp (DepsEnv -> a)  
  | ErrorOp Error

instance Functor EvalOp where
  fmap f (LogOp s x) = LogOp s $ f x
  fmap f (ReadOp k) = ReadOp $ f . k
  fmap _ (ErrorOp e) = ErrorOp e

type EvalM a = Free EvalOp a 

depsLog :: InnerDepVal -> EvalM ()
depsLog bdv = Free $ LogOp bdv $ pure ()

askEnv :: EvalM DepsEnv
askEnv = Free $ ReadOp $ \env -> pure env

modifyEffects :: (Functor e, Functor h) => (e (Free e a) -> h (Free e a)) -> Free e a -> Free h a
modifyEffects _ (Pure x) = Pure x
modifyEffects g (Free e) = Free $ modifyEffects g <$> g e

localEnv :: (DepsEnv -> DepsEnv) -> EvalM a -> EvalM a
localEnv f = modifyEffects g
  where
    g (ReadOp k) = ReadOp $ k . f
    g op = op

failure :: String -> EvalM a
failure = Free . ErrorOp

-- | General environment functions. Relies heavily on module data.map
envEmpty :: DepsEnv
envEmpty = M.empty

envSingle :: Maybe NestedVName -> DepVal -> Either Error DepsEnv
envSingle names d = envExtend names d envEmpty 

envExtend :: Maybe NestedVName -> DepVal -> DepsEnv -> Either Error DepsEnv
envExtend (Just (Name vn)) d env = Right $ M.insert vn d env
envExtend (Just (Tuple nest)) (DepTuple tpl) env
  | length nest == length tpl = foldr envUnionError (Right env) $ map (\(x, y) -> envSingle x y) $ zip (map Just nest) tpl
  | otherwise = Left $ 
      "Tried to extend environment with patterns of different dimensions: "
      ++ (show $ Tuple nest) ++ "\n : " ++ show tpl
envExtend (Just (Tuple nest)) d _ = Left $ 
      "Tried to extend environment with patterns of different dimensions: "
      ++ (show $ Tuple nest) ++ "\n : " ++ show d
envExtend (Just WildcardName) _ env = Right env
envExtend Nothing _ env = Right env
-- Could argue that throwing an error instead is better for the wildcard case,
-- i.e. in AST bindings of "Let _ = 3 + 4 in ..."

envUnionError :: Either Error DepsEnv -> Either Error DepsEnv -> Either Error DepsEnv
envUnionError (Left e) _ = Left e
envUnionError  _ (Left e) = Left e
envUnionError (Right env1) (Right env2) = Right $ envUnion env1 env2

envLookup :: VName -> DepsEnv -> EvalM DepVal
envLookup vn env = do
  case M.lookup vn env of
    Just x -> pure x
    Nothing -> failure $ "Unknown variable: " <> (show vn)

envUnion :: DepsEnv -> DepsEnv -> DepsEnv
envUnion = M.union

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
depValDeps (DepTuple x) = foldMap depValDeps x
depValDeps (DepFun _ lst eb) = foldr idsWithout (Ids $ freeVarsList eb) $ concat $ map nestedVNameDeps lst
    where nestedVNameDeps :: NestedVName -> [VName]
          nestedVNameDeps (Name vn) = [vn]
          nestedVNameDeps (Tuple x) = concat $ map nestedVNameDeps x
          nestedVNameDeps WildcardName = mempty

-- | Joins two different sets of DepVal
-- Only tuples of equal length can be joined without collapsing to pure DepVal Deps
depValJoin :: DepVal -> DepVal -> DepVal
depValJoin (DepTuple xs) (DepTuple ys)
  | length xs == length ys = DepTuple $ zipWith depValJoin xs ys
depValJoin x y = DepVal $ depValDeps x <> depValDeps y

-- | Injects dependencies into expressions which is useful in conditionals
depValInj :: Deps -> DepVal -> DepVal
depValInj x (DepVal y) = DepVal $ x <> y
depValInj x (DepTuple ys) = DepTuple $ map (depValInj x) ys
depValInj x v = DepVal $ x <> depValDeps v

-- | Locates free variables in the body of ProgBase
-- OBS: Only handles the last progDecs currently
depsFreeVarsInProgBase :: ProgBase Info VName -> DepsEnv
depsFreeVarsInProgBase base =
  case last $ progDecs base of 
    ValDec valbind -> depsFreeVarsInExpBase $ valBindBody valbind
    _ -> envEmpty -- Should not return envEmpty

-- | Dependencies in ExpBase 
depsFreeVarsInExpBase :: ExpBase Info VName -> DepsEnv
depsFreeVarsInExpBase eb = M.fromList $ map (\x -> (x, DepVal $ idsSingle x)) $ freeVarsList eb

-- | ExpBase to list of free variables in the form of VName's
freeVarsList :: ExpBase Info VName -> [VName]
freeVarsList eb = S.toList $ FV.fvVars $ freeInExp eb

-- | Converts pattern bases to pure NestedVNames ** UNFINISHED
stripPatBase :: PatBase Info VName t -> NestedVName
stripPatBase (TuplePat pb_n _) = Tuple (map stripPatBase pb_n)
stripPatBase (Id vn _ _) = Name vn
stripPatBase (PatParens pb _) = stripPatBase pb
stripPatBase (PatAscription pb _ _) = stripPatBase pb
stripPatBase _ = WildcardName

-- | Converts nested names to pure DepsEnv's, should be used with care
nestedNamesToSelfEnv :: NestedVName -> DepsEnv
nestedNamesToSelfEnv (Name vn) = M.singleton vn $ DepVal $ idsSingle vn
nestedNamesToSelfEnv (Tuple nvn) = foldr envUnion envEmpty (map nestedNamesToSelfEnv nvn)
nestedNamesToSelfEnv WildcardName = envEmpty

-- | Finds dependencies in declaration bases
depsDecBase :: DecBase Info VName -> EvalM DepVal
depsDecBase (ValDec bindings) = do
  env <- askEnv
  let env' = nestedNamesToSelfEnv $ Tuple (map stripPatBase (valBindParams bindings)) 
    in localEnv (const $ env' `envUnion` env) (depsExpBase $ valBindBody bindings)
    -- ^^ envUnion above might be dangerous (prefers env' over env in duplicates)
depsDecBase (TypeDec _) = failure "Does not support analysis of TypeDec"
depsDecBase (ModTypeDec _) = failure "Does not support analysis of ModTypeDec"
depsDecBase (ModDec _) = failure "Does not support analysis of ModDec"
depsDecBase (OpenDec _ _) = failure "Does not support analysis of OpenDec"
depsDecBase (LocalDec db _) = depsDecBase db 
depsDecBase (ImportDec _ _ _) = failure "Does not support analysis of ImportDec"

-- | Finds dependencies in expression bases
depsExpBase :: ExpBase Info VName -> EvalM DepVal
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
  pure $ DepTuple d_n
depsExpBase (RecordLit fb_n _) = do
  d_n <- mapM depsFieldBase fb_n
  pure $ foldr depValJoin (DepVal mempty) d_n
depsExpBase (ArrayLit eb_n _ _) = do
  d_n <- mapM depsExpBase eb_n
  pure $ foldr depValJoin (DepVal mempty) d_n
depsExpBase (ArrayVal _ _ _) = pure $ DepVal mempty
depsExpBase (Attr _ eb _) = depsExpBase eb 
depsExpBase (Project name eb _ _) = do -- OBS, name has to be integer??
  d1 <- depsExpBase eb
  pure $
    case (d1, readMaybe (nameToString name) :: Maybe Int) of
      (DepTuple x, Just i) | i < length x -> x !! i
      (x, _) -> x 
depsExpBase (Negate eb _) = depsExpBase eb
depsExpBase (Not eb _) = depsExpBase eb
depsExpBase (Assert eb1 eb2 _ _) = do
  d1 <- depsExpBase eb1
  d2 <- depsExpBase eb2
  pure $ d1 `depValJoin` d2
depsExpBase (Constr _ eb_n _ _) = do
  d_n <- mapM depsExpBase eb_n
  pure $ foldr depValJoin (DepVal mempty) d_n
depsExpBase (Update eb1 sb eb2 _) = do
  d1 <- depsExpBase eb1
  d2 <- depsExpBase eb2
  d_n <- depsSliceBase sb
  pure $ foldr depValJoin (d1 `depValJoin` d2) d_n
depsExpBase (RecordUpdate eb1 _ eb2 _ _) = do
  d1 <- depsExpBase eb1
  d2 <- depsExpBase eb2
  pure $ d1 `depValJoin` d2
depsExpBase (OpSection qn _ _) = do
  env <- askEnv
  envLookup (qualLeaf qn) env
depsExpBase (OpSectionLeft qn _ eb _ _ _) = do
  env <- askEnv
  d1 <- envLookup (qualLeaf qn) env
  d2 <- depsExpBase eb
  pure $ d1 `depValJoin` d2
depsExpBase (OpSectionRight qn _ eb _ _ _) = do
  env <- askEnv
  d1 <- envLookup (qualLeaf qn) env
  d2 <- depsExpBase eb
  pure $ d1 `depValJoin` d2
depsExpBase (ProjectSection _ _ _) = pure $ DepVal mempty
depsExpBase (IndexSection sb _ _) = do
  d_n <- depsSliceBase sb
  pure $ foldr depValJoin (DepVal mempty) d_n
depsExpBase (Ascript eb te _) = do
  d1 <- depsExpBase eb
  d2 <- depsTypeExp te
  pure $ d1 `depValJoin` d2
depsExpBase (Coerce eb te _ _) = do
  d1 <- depsExpBase eb
  d2 <- depsTypeExp te
  pure $ d1 `depValJoin` d2  
depsExpBase (Lambda pb_n eb _ _ _) = do
  env <- askEnv
  let names = map stripPatBase pb_n
    in pure $ DepFun env names eb
depsExpBase (AppExp aeb _) = depsAppExpBase aeb

-- | Finds dependencies in field bases
depsFieldBase :: FieldBase Info VName -> EvalM DepVal
depsFieldBase (RecordFieldExplicit _ eb _) = depsExpBase eb
depsFieldBase (RecordFieldImplicit (L _ vn) _ _) = do
  env <- askEnv
  envLookup vn env  

-- | Finds dependencies in application expression bases
depsAppExpBase :: AppExpBase Info VName -> EvalM DepVal
depsAppExpBase (Apply eb1 lst _) = do
  d1 <- depsExpBase eb1
  d_n <- mapM depsExpBase $ map snd (NE.toList lst)
  case d1 of 
    DepFun env n_n body -> do
      env' <- case foldr envUnionError (Right env) $ zipWith envSingle (map Just n_n) d_n of
        Left e -> failure e
        Right e -> pure e 
      localEnv (const env') $ depsExpBase body
    _ -> pure $ foldr depValJoin d1 d_n
depsAppExpBase (Range eb1 maybe_eb2 _ _) = do
  d1 <- depsExpBase eb1
  d2 <- maybe (pure $ DepVal mempty) depsExpBase maybe_eb2
  pure $ d1 `depValJoin` d2
depsAppExpBase (LetPat _ pb eb1 eb2 _) = do
  d1 <- depsExpBase eb1
  env <- askEnv
  let name = stripPatBase pb
    in do
      case d1 of
        DepFun _ _ eb3 -> depsLog $ Depends name $ DepVal $ Ids $ freeVarsList eb3
         -- ^ Might lose some precision but it is to be able to represent
         -- dependencies without abstract information 
         -- This is partly because we don't know on which parameters the function is evaluated
        _ -> depsLog $ Depends name d1
      env' <- case envExtend (Just name) d1 env of
        (Left e) -> failure e
        (Right e) -> pure e
      localEnv (const env') $ depsExpBase eb2
depsAppExpBase (LetFun _ _ _ _) = pure $ DepVal mempty -- OBS
depsAppExpBase (If eb1 eb2 eb3 _) = do
  d1 <- depsExpBase eb1
  d2 <- depsExpBase eb2
  d3 <- depsExpBase eb3
  pure $ depValDeps d1 `depValInj` (d2 `depValJoin` d3)
depsAppExpBase (Loop _ pb lib lfb eb  _) = 
  let vn = stripPatBase pb
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
          let vn' = Just $ stripPatBase pb'
            in do
              d2 <- localEnv (const loop_env) $ depsExpBase eb'
              d3 <- loop vn vn' d1
              pure $ depValDeps d2 `depValInj` d3
        While eb' -> do
          d2 <- localEnv (const loop_env) $ depsExpBase eb'
          d3 <- loop vn Nothing d1
          pure $ depValDeps d2 `depValInj` d3
      where loop :: NestedVName -> Maybe NestedVName -> DepVal -> EvalM DepVal
            loop p i ld = do
                  env  <- askEnv
                  env' <- case (envSingle i (DepVal mempty), envSingle (Just p) ld) of
                            (Left e, _) -> failure e
                            (_, Left e) -> failure e
                            (Right env1, Right env2) -> pure $ env `envUnion` env1 `envUnion` env2
                  ld' <- localEnv (const env') (depsExpBase eb)
                  if ld == ld'
                    then pure ld'
                    else loop p i $ ld `depValJoin` ld' 
depsAppExpBase (BinOp _ _ eb1 eb2 _) = do
  d1 <- depsExpBase $ fst eb1
  d2 <- depsExpBase $ fst eb2
  pure $ d1 `depValJoin` d2
depsAppExpBase (LetWith _ _ _ _ _ _) = pure $ DepVal mempty -- OBS
depsAppExpBase (Index eb sb _) = do
  d <- depsExpBase eb 
  d_n <- depsSliceBase sb
  pure $ foldr depValJoin d d_n 
depsAppExpBase (Match eb ne_cb _) = do
  d1 <- depsExpBase eb
  d_n <- mapM depsCaseBase (NE.toList ne_cb)
  pure $ foldr depValJoin (DepVal mempty) $ map (\x -> depValInj (depValDeps x) d1) d_n
  -- OBS use of injection (might need to be removed)

-- | Finds dependencies in case bases
depsCaseBase :: CaseBase Info VName -> EvalM DepVal
depsCaseBase (CasePat pb eb _) = do 
  d1 <- depsPatBase pb
  d2 <- depsExpBase eb
  pure $ depValDeps d1 `depValInj` d2 -- OBS use of injection here (might need to be removed)

-- | Finds dependencies in dimension index bases
depsDimIndexBase :: DimIndexBase Info VName -> EvalM DepVal
depsDimIndexBase (DimFix eb) = depsExpBase eb
depsDimIndexBase (DimSlice maybe_eb1 maybe_eb2 maybe_eb3) = do
  d1 <- maybe (pure $ DepVal mempty) depsExpBase maybe_eb1
  d2 <- maybe (pure $ DepVal mempty) depsExpBase maybe_eb2
  d3 <- maybe (pure $ DepVal mempty) depsExpBase maybe_eb3
  pure $ d1 `depValJoin` d2 `depValJoin` d3

-- | Finds dependencies in pattern bases
depsPatBase :: PatBase Info VName t -> EvalM DepVal
depsPatBase (TuplePat pb_n _) = do
  d_n <- mapM depsPatBase pb_n
  pure $ DepTuple d_n 
depsPatBase (RecordPat rcrd _) = do
  d_n <- mapM (depsPatBase . snd) rcrd
  pure $ foldr depValJoin (DepVal mempty) d_n
depsPatBase (PatParens pb _) = depsPatBase pb
depsPatBase (Id vn _ _) = pure $ DepVal $ Ids [vn]
depsPatBase (Wildcard _ _) = pure $ DepVal mempty
depsPatBase (PatAscription pb te _) = do
  d1 <- depsPatBase pb
  d2 <- depsTypeExp te
  pure $ d1 `depValJoin` d2
depsPatBase (PatLit _ _ _) = pure $ DepVal mempty
depsPatBase (PatConstr _ _ pb_n _) = do
  d_n <- mapM depsPatBase pb_n
  pure $ foldr depValJoin (DepVal mempty) d_n
depsPatBase (PatAttr _ pb _) = depsPatBase pb

-- | Finds dependencies in type expressions
depsTypeExp :: TypeExp (ExpBase Info VName) VName -> EvalM DepVal
depsTypeExp (TEVar qn _) = do
  env <- askEnv
  envLookup (qualLeaf qn) env
depsTypeExp (TEParens te _) = depsTypeExp te
depsTypeExp (TETuple te_n _) = do
  d_n <- mapM depsTypeExp te_n
  pure $ DepTuple d_n
depsTypeExp (TERecord lst _) = do
  d_n <- mapM (depsTypeExp . snd) lst
  pure $ foldr depValJoin (DepVal mempty) d_n
depsTypeExp (TEArray se te _ ) = do
   d1 <- depsSizeExp se
   d2 <- depsTypeExp te
   pure $ d1 `depValJoin` d2
depsTypeExp (TEUnique te _) = depsTypeExp te
depsTypeExp (TEApply te tae _) = do -- OBS
  d1 <- depsTypeExp te
  d2 <- depsTypeArgExp tae
  pure $ d1 `depValJoin` d2
depsTypeExp (TEArrow maybe_vn te1 te2 _) = do
  d1 <- depsTypeExp te1
  d2 <- depsTypeExp te2
  case maybe_vn of
    Just x -> do
      env <- askEnv
      d3 <- envLookup x env
      pure $ d1 `depValJoin` d2 `depValJoin` d3
    Nothing -> pure $ d1 `depValJoin` d2
depsTypeExp (TESum lst _) = do
  d_n <- mapM inner (map snd lst)
  pure $ foldr depValJoin (DepVal mempty) d_n
  where inner x_n = do
                      d_n' <- mapM depsTypeExp x_n
                      pure $ foldr depValJoin (DepVal mempty) d_n'  
depsTypeExp (TEDim vn_n te _) = do
  env <- askEnv
  d_n <- mapM (\x -> envLookup x env) vn_n
  d1 <- depsTypeExp te
  pure $ foldr depValJoin d1 d_n

-- | Finds dependencies in type argument expressions
depsTypeArgExp :: TypeArgExp (ExpBase Info VName) VName -> EvalM DepVal
depsTypeArgExp (TypeArgExpSize se) = depsSizeExp se
depsTypeArgExp (TypeArgExpType te) = depsTypeExp te

-- | Finds dependencies in size expressions
depsSizeExp :: SizeExp (ExpBase Info VName) -> EvalM DepVal
depsSizeExp (SizeExp eb _) = depsExpBase eb
depsSizeExp (SizeExpAny _) = pure $ DepVal mempty

-- | Finds dependencies in slice bases
depsSliceBase :: SliceBase Info VName -> EvalM [DepVal]
depsSliceBase = mapM depsDimIndexBase

bindingNameInDecBase :: DecBase Info VName -> Maybe VName
bindingNameInDecBase (ValDec bindings) = Just $ valBindName bindings
bindingNameInDecBase (LocalDec db _) = bindingNameInDecBase db 
bindingNameInDecBase _ = Nothing

-- | Recursive executer of evaluation
logDepsM :: DepsEnv -> EvalM DepVal -> (Either Error DepVal, [InnerDepVal])
logDepsM _ (Pure x) = (Right x, [])
logDepsM env (Free (ReadOp k)) = logDepsM env $ k env
logDepsM env (Free (LogOp d1 x)) =
  let (y, d2) = logDepsM env x
    in (y, d2 ++ [d1])
logDepsM _ (Free (ErrorOp e)) = (Left e, [])

-- | Interpretation function for dependencies
deps' :: DepsEnv -> Prog -> [(Maybe VName, (Either Error DepVal, [InnerDepVal]))]
deps' env prog = zip
                  (map bindingNameInDecBase $ progDecs prog)
                  (map (logDepsM env . depsDecBase) $ progDecs prog)

-- | Finds dependencies in a program
deps :: Prog -> String
deps prog = foldr concatDeps "" $ deps' (depsFreeVarsInProgBase prog) prog
  where
        concatDeps (Nothing, _) acc = acc
        concatDeps (Just vn, (Left e, _)) acc =
                  "\ESC[31mError in dependency interpreter in function: \ESC[36m" ++ show vn ++
                  "\n\ESC[0m\tError message: " ++ e ++ "\n" ++ acc 
        concatDeps (Just vn, (Right a, d_n)) acc =
                  "Function: \ESC[95m" ++ show vn ++
                  "\n\ESC[0m\tDependencies: \ESC[36m" ++ show a ++ 
                  "\n\ESC[0m\tInner dependencies: \ESC[36m" ++ show d_n ++ "\ESC[0m\n" ++ acc 

-- | Function for unit-testing specific parts of the ast
depsTestExp :: ExpBase Info VName -> Either Error (DepVal, [InnerDepVal]) 
depsTestExp eb =
  case logDepsM (depsFreeVarsInExpBase eb) $ depsExpBase eb of
    (Left e, _) -> Left e 
    (Right d, id_n) -> Right (d, id_n)
 