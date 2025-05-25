-- | Finds dependencies between variables in programs
module Language.Futhark.Deps
  ( deps,
    depsTestExp,
    DepVal (..),
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
import Data.List (sortOn, elemIndex)

type Error = String

newtype Ids = Ids [VName]
  deriving (Eq, Show)

type Deps = Ids

data Struct = DepRecord | DepTuple 
  deriving (Eq, Show)

data DepVal
  = DepVal Ids
  | DepGroup Struct [(Name, DepVal)]
  | DepFun DepsEnv [NestedVName] (ExpBase Info VName)
  deriving (Eq, Show)

data BoundDepVal
  = Depends VName DepVal
  | None
  deriving Show

type InnerDepVals = DepsEnv

newtype DepsEnv = Env (M.Map VName DepVal)
  deriving (Eq, Show)

data NestedVName
  = Name VName
  | RecordName [(Name, NestedVName)] 
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
  = LogOp DepsEnv a
  | ReadOp (DepsEnv -> a)  
  | ErrorOp Error

instance Functor EvalOp where
  fmap f (LogOp s x) = LogOp s $ f x
  fmap f (ReadOp k) = ReadOp $ f . k
  fmap _ (ErrorOp e) = ErrorOp e

type EvalM a = Free EvalOp a 

depsLog :: DepsEnv -> EvalM ()
depsLog env = Free $ LogOp env $ pure ()

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

envSingle :: Maybe NestedVName -> DepVal -> Either Error DepsEnv
envSingle names d = envExtend names d mempty

envSinglePure :: VName -> DepVal -> DepsEnv
envSinglePure vn d = Env $ M.singleton vn d

envExtend :: Maybe NestedVName -> DepVal -> DepsEnv -> Either Error DepsEnv
envExtend (Just (Name vn)) d (Env env) = Right $ Env $ M.insert vn d env
envExtend (Just (RecordName [])) (DepGroup _ []) env = Right env
envExtend (Just (RecordName r1)) (DepGroup _ r2) env =
  let (names1, tpl1) = unzip r1
      (names2, tpl2) = unzip r2 
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

envUnionError :: Either Error DepsEnv -> Either Error DepsEnv -> Either Error DepsEnv
envUnionError (Left e) _ = Left e
envUnionError  _ (Left e) = Left e
envUnionError (Right env1) (Right env2) = Right $ env1 <> env2

envLookup :: VName -> DepsEnv -> EvalM DepVal
envLookup vn (Env env) = do
  case M.lookup vn env of
    Just x -> pure x
    Nothing -> failure $ "Unknown variable: " <> (show vn)

createRecordTuple :: [a] -> [(Name, a)]
createRecordTuple lst = zip (map (nameFromString . show) [0 .. length lst]) lst

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


instance Semigroup DepsEnv where
  Env x <> Env y = Env $ x `M.union` y 

instance Monoid DepsEnv where
  mempty = Env $ M.empty

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
depValDeps (DepGroup _ x) = foldMap depValDeps $ map snd x
depValDeps (DepFun _ lst eb) = foldr idsWithout (Ids $ freeVarsList eb) $ concat $ map nestedVNameDeps lst
    where nestedVNameDeps :: NestedVName -> [VName]
          nestedVNameDeps (Name vn) = [vn]
          nestedVNameDeps (RecordName x) = concat $ map (nestedVNameDeps . snd) x
          nestedVNameDeps WildcardName = mempty

-- | Joins two different sets of DepVal
-- Only records of equal length and fields can be joined without collapsing to pure DepVal Deps
depValJoin :: DepVal -> DepVal -> DepVal
depValJoin x@(DepGroup t xs) y@(DepGroup _ ys) =
  let (names1, tpl1) = unzip xs
      (names2, tpl2) = unzip ys
    in
      if names1 == names2 
        then DepGroup t $ zip names1 $ zipWith depValJoin tpl1 tpl2
        else DepVal $ depValDeps x <> depValDeps y
depValJoin x y = DepVal $ depValDeps x <> depValDeps y

-- | Injects dependencies into expressions which is useful in conditionals
depValInj :: Deps -> DepVal -> DepVal
depValInj x (DepVal y) = DepVal $ x <> y
depValInj x (DepGroup t ys) = 
  let (names, tpl) = unzip ys
    in DepGroup t $ zip names $ map (depValInj x) tpl
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
depsFreeVarsInExpBase eb = Env $ M.fromList $ map (\x -> (x, DepVal $ idsSingle x)) $ freeVarsList eb

-- | ExpBase to list of free variables in the form of VName's
freeVarsList :: ExpBase Info VName -> [VName]
freeVarsList eb = S.toList $ FV.fvVars $ freeInExp eb

-- | Converts pattern bases to pure NestedVNames ** UNFINISHED
extractPatBaseName :: PatBase Info VName t -> NestedVName
extractPatBaseName (TuplePat pb_n _) = RecordName $ createRecordTuple (map extractPatBaseName pb_n)
extractPatBaseName (RecordPat npb_n _) = RecordName $ sortOn fst $ map (\(L _ x, y) -> (x, extractPatBaseName y)) npb_n
extractPatBaseName (PatParens pb _) = extractPatBaseName pb
extractPatBaseName (Id vn _ _) = Name vn
extractPatBaseName (PatAscription pb _ _) = extractPatBaseName pb
extractPatBaseName _ = WildcardName
-- Missing: PatConst and PatAttr


-- | Converts nested names to pure DepsEnv's, should be used with care
nestedNamesToSelfEnv :: NestedVName -> DepsEnv
nestedNamesToSelfEnv (Name vn) = Env $ M.singleton vn $ DepVal $ idsSingle vn
nestedNamesToSelfEnv (RecordName nv_n) = foldMap (nestedNamesToSelfEnv . snd) nv_n
nestedNamesToSelfEnv WildcardName = mempty

-- | Finds dependencies in declaration bases
depsDecBase :: DecBase Info VName -> EvalM DepVal
depsDecBase (ValDec bindings) = do
  env <- askEnv
  let env' = foldMap (nestedNamesToSelfEnv . extractPatBaseName) $ valBindParams bindings
    in localEnv (const $ env' <> env) (depsExpBase $ valBindBody bindings)
    -- ^^ envUnion above might be dangerous (prefers env' over env in duplicates)
depsDecBase (TypeDec _) = failure "Does not support analysis of TypeDec"
depsDecBase (ModTypeDec _) = failure "Does not support analysis of ModTypeDec"
depsDecBase (ModDec _) = failure "Does not support analysis of ModDec"
depsDecBase (OpenDec _ _) = failure "Does not support analysis of OpenDec"
depsDecBase (LocalDec db _) = depsDecBase db 
depsDecBase (ImportDec _ _ _) = failure "Does not support analysis of ImportDec"
-- ^ The above errors will not be thrown if evaluated using deps' for prettier printing

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
  pure $ DepGroup DepTuple $ createRecordTuple d_n
depsExpBase (RecordLit fb_n _) = do
  d_n <- mapM depsFieldBase fb_n
  pure $ DepGroup DepRecord $ sortOn fst $ zip (map extractFieldBaseName fb_n) d_n
  where extractFieldBaseName :: FieldBase Info VName -> Name
        extractFieldBaseName (RecordFieldExplicit (L _ name) _ _) = name
        extractFieldBaseName (RecordFieldImplicit (L _ (VName name _)) _ _) = name
depsExpBase (ArrayLit eb_n _ _) = do
  d_n <- mapM depsExpBase eb_n
  pure $ foldr depValJoin (DepVal mempty) d_n
depsExpBase (ArrayVal _ _ _) = pure $ DepVal mempty
depsExpBase (Attr _ eb _) = depsExpBase eb 
depsExpBase (Project name eb _ _) = do
  d1 <- depsExpBase eb
  case d1 of
    (DepGroup _ r) ->
      let (names, tpl) = unzip r
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
  pure $ d1 `depValJoin` d2
depsExpBase (Constr _ eb_n _ _) = do
  d_n <- mapM depsExpBase eb_n
  pure $ foldr depValJoin (DepVal mempty) d_n
depsExpBase (Update eb1 sb eb2 _) = do
  d1 <- depsExpBase eb1
  d2 <- depsExpBase eb2
  d_n <- depsSliceBase sb
  pure $ foldr depValJoin (d1 `depValJoin` d2) d_n
depsExpBase (RecordUpdate eb1 _ eb2 _ _) = do -- OBS
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
  let names = map extractPatBaseName pb_n
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
depsAppExpBase (Apply eb lst _) = do
  d1 <- depsExpBase eb
  d_n <- mapM depsExpBase $ map snd (NE.toList lst)
  case d1 of 
    DepFun env' n_n body -> do
      fun_env <- case foldr envUnionError (Right env') $ zipWith envSingle (map Just n_n) d_n of
        Left e -> failure e
        Right e -> pure e 
      localEnv (const fun_env) $ depsExpBase body
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
      log' d1 name
      env' <- case envExtend (Just name) d1 env of
        (Left e) -> failure e
        (Right e) -> pure e
      localEnv (const env') $ depsExpBase eb2
      where log' :: DepVal -> NestedVName -> EvalM ()
            log' d (Name vn) = depsLog $ envSinglePure vn $ DepVal $ depValDeps d
            log' _ (RecordName []) = pure ()
            log' (DepGroup t (a:b)) (RecordName (c:d)) = do
              log' (snd a) (snd c) -- OBS
              log' (DepGroup t b) (RecordName d)
            log' _ WildcardName = pure ()
            log' a b = failure $ "Failed to log an inner dependence between " <> show b <> " and " <> show a 
depsAppExpBase (LetFun _ _ _ _) = pure $ DepVal mempty -- OBS
depsAppExpBase (If eb1 eb2 eb3 _) = do
  d1 <- depsExpBase eb1
  d2 <- depsExpBase eb2
  d3 <- depsExpBase eb3
  pure $ depValDeps d1 `depValInj` (d2 `depValJoin` d3)
depsAppExpBase (Loop _ pb lib lfb eb  _) = 
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
      where loop :: NestedVName -> Maybe NestedVName -> DepVal -> EvalM DepVal
            loop p i ld = do
                  env  <- askEnv
                  env' <- case (envSingle i (DepVal mempty), envSingle (Just p) ld) of
                            (Left e, _) -> failure e
                            (_, Left e) -> failure e
                            (Right env1, Right env2) -> pure $ env <> env1 <> env2
                  ld' <- localEnv (const env') (depsExpBase eb)
                  if ld == ld'
                    then pure ld'
                    else loop p i $ ld `depValJoin` ld' 
depsAppExpBase (BinOp qn _ eb1 eb2 _) = do
  env <- askEnv
  d1 <- envLookup (qualLeaf $ fst qn) env
  d2 <- depsExpBase $ fst eb1
  d3 <- depsExpBase $ fst eb2
  pure $ d1 `depValJoin` d2 `depValJoin` d3
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
  pure $ DepGroup DepTuple $ createRecordTuple d_n 
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
  pure $ DepGroup DepTuple $ createRecordTuple d_n
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

-- | Recursive executer of evaluation
logDepsM :: DepsEnv -> EvalM DepVal -> (Either Error DepVal, InnerDepVals)
logDepsM _ (Pure x) = (Right x, mempty)
logDepsM env (Free (ReadOp k)) = logDepsM env $ k env
logDepsM env (Free (LogOp d1 x)) =
  let (y, d2) = logDepsM env x
    in (y, d2 <> d1)
logDepsM _ (Free (ErrorOp e)) = (Left e, mempty)

-- Finds the relation between the name and the explicit ExpBase definition i a DecBase
bindingInDecBase :: DecBase Info VName -> BoundDepVal
bindingInDecBase (ValDec bind) = 
  let func = DepFun mempty (map extractPatBaseName $ valBindParams bind) (valBindBody bind)
    in Depends (valBindName bind) func
bindingInDecBase (LocalDec db _) = bindingInDecBase db 
bindingInDecBase _ = None

-- | Interpretation function for dependencies
deps' :: DepsEnv -> Prog -> [(Either (Maybe VName, Error) (Maybe VName, DepVal, InnerDepVals))]
deps' env prog = 
  let bindings = map bindingInDecBase $ progDecs prog
      env' = foldMap joinBindings bindings -- A two pass scan*
        where joinBindings :: BoundDepVal -> DepsEnv
              joinBindings (Depends vn d) = envSinglePure vn d
              joinBindings _ = mempty 
  in map repack $ zip bindings $ map (logDepsM (env' <> env) . depsDecBase) $ progDecs prog
        where repack :: (BoundDepVal, (Either Error DepVal, InnerDepVals)) -> (Either (Maybe VName, Error) (Maybe VName, DepVal, InnerDepVals))
              repack (Depends vn _, (Right d2, d3)) = Right (Just vn, d2, d3)
              repack (None, (Right d2, d3)) = Right (Nothing, d2, d3)
              repack (Depends vn _, (Left e, _)) = Left $ (Just vn, e) 
              repack (None, (Left e, _)) = Left $ (Nothing, e) 
-- *Turns out this is unnecessary since Futhark doesn't do support functions defined later in the program :-)  

-- | Finds dependencies in a program
deps :: Prog -> String
deps prog = foldr concatDeps "" $ deps' (depsFreeVarsInProgBase prog) prog
  where concatDeps :: Either (Maybe VName, Error) (Maybe VName, DepVal, InnerDepVals) -> String -> String
        concatDeps (Right (vn, d, Env d_n)) acc =
                  "Function: \ESC[95m" ++ show vn ++
                  "\n\ESC[0m\tDependencies: \ESC[36m" ++ show d ++ 
                  "\n\ESC[0m\tInner dependencies: \ESC[36m" ++ 
                  (foldr (\(k, a) x -> x ++ "\n\t\t" ++ show k ++ " depends on " ++ show a) "" $ M.toList d_n)
                  ++ "\ESC[0m\n" ++ acc 
        concatDeps (Left (vn, e)) acc =
                  "\ESC[31mError in dependency interpreter in function: \ESC[95m" ++ show vn ++
                  "\n\ESC[0m\tError message: " ++ e ++ "\n" ++ acc 

-- | Function for unit-testing specific parts of the ast
depsTestExp :: ExpBase Info VName -> Either Error (DepVal, DepsEnv) 
depsTestExp eb =
  case logDepsM (depsFreeVarsInExpBase eb) $ depsExpBase eb of
    (Left e, _) -> Left e 
    (Right d, id_n) -> Right (d, id_n)
 