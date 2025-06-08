{-# LANGUAGE ScopedTypeVariables #-}

-- | Finds dependencies between variables in programs
module Language.Futhark.Deps
  ( runDeps,
    testDeps,
    DepVal (..),
    BoundDepVal (..),
    NestedName (..),
    InnerDepVals,
    DepsEnv,
    StackTrace (..),
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

newtype StackTrace = CallStack [VName]
  deriving (Eq, Show, Ord)

emptyStack :: StackTrace
emptyStack = CallStack []

addToStack :: VName -> StackTrace -> StackTrace
addToStack vn (CallStack st) = CallStack (st ++ [vn])  

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
  | DepFun (Maybe VName) DepsEnv [NestedName] (ExpBase Info VName)
  deriving (Eq, Show)
-- The first (Maybe VName) certainly be omitted, but this is somehow easier
-- (it is used to track the call stack)

data BoundDepVal
  = Depends VName DepVal
  | None (Maybe DepVal) -- In case we need BoundDepVal to act as a normal DepVal
  deriving (Eq, Show)

-- An environment mapping keys to values, 
newtype Env k a = Env (M.Map k a)
  deriving (Eq, Show)

type DepsEnv = Env VName DepVal
type InnerDepVals = Env StackTrace DepVal

instance Semigroup DepsEnv where
  Env x <> Env y = Env $ x `M.union` y 

instance Monoid DepsEnv where
  mempty = Env $ M.empty

-- A data-type of a stack-trace and a dependence environment


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
  = LogOp (StackTrace, VName, DepVal) a
  | ReadOp ((DepsEnv, StackTrace) -> a)  
  | ErrorOp Error

instance Functor InterpretOp where
  fmap f (LogOp s x) = LogOp s $ f x
  fmap f (ReadOp k) = ReadOp $ f . k
  fmap _ (ErrorOp e) = ErrorOp e

-- Interpreter monad
type InterpretM a = Free InterpretOp a 


-- General environment functions
askEnv :: InterpretM (DepsEnv, StackTrace)
askEnv = Free $ ReadOp $ \env -> pure env

modifyEffects :: (Functor e, Functor h)
              => (e (Free e a)
              -> h (Free e a))
              -> Free e a
              -> Free h a
modifyEffects _ (Pure x) = Pure x
modifyEffects g (Free e) = Free $ modifyEffects g <$> g e

localEnv :: ((DepsEnv, StackTrace) -> (DepsEnv, StackTrace))
         -> InterpretM a
         -> InterpretM a
localEnv f = modifyEffects g
  where
    g (ReadOp k) = ReadOp $ k . f
    g op = op

failure :: String -> InterpretM a
failure = Free . ErrorOp

depsEnvSingle :: Maybe NestedName -> DepVal -> Either Error (DepsEnv, StackTrace)
depsEnvSingle names d = depsEnvExtend names d depsEnvEmpty

depsEnvExtend :: Maybe NestedName
              -> DepVal
              -> (DepsEnv, StackTrace)
              -> Either Error (DepsEnv, StackTrace)
depsEnvExtend (Just (Name vn)) d (Env env, st) =
  Right $ (Env $ M.insert vn d env, st)
depsEnvExtend (Just (RecordName r1)) (DepGroup _ r2) env
  | null r1 && null r2 = Right env
  | otherwise =
    let (names1, tpl1) = unzip $ TPL.sortFields r1
        (names2, tpl2) = unzip $ TPL.sortFields r2 
      in
        if names1 == names2
          then foldr envUnionError (Right env) $
                 map (\(x, y) -> depsEnvSingle (Just x) y) $ zip tpl1 tpl2
          else Left $ "Tried to extend environment non-matching records: " <>
                show r1 <> "\tand:\t" <> show r2
depsEnvExtend (Just (RecordName r)) d _ = Left $ 
      "Tried to extend environment with patterns of different dimensions: "
      ++ show r ++ "\tand:\t" ++ show d
depsEnvExtend (Just WildcardName) _ env = Right env
depsEnvExtend Nothing _ env = Right env

depsEnvExtendPure :: VName
                  -> DepVal
                  -> (DepsEnv, StackTrace) 
                  -> (DepsEnv, StackTrace)
depsEnvExtendPure vn d ((Env env, st)) = (Env $ M.insert vn d env, st)

depsEnvEmpty :: (DepsEnv, StackTrace)
depsEnvEmpty = (Env M.empty, emptyStack)

envUnionError :: Either Error (DepsEnv, StackTrace) 
              -> Either Error (DepsEnv, StackTrace) 
              -> Either Error (DepsEnv, StackTrace)
envUnionError (Left e) _ = Left e
envUnionError  _ (Left e) = Left e
envUnionError (Right (Env env1, _)) (Right (Env env2, _)) =
  Right (Env $ env2 <> env1, emptyStack)

envLookup :: VName -> (DepsEnv, StackTrace) -> InterpretM DepVal
envLookup vn ((Env env, _)) = do
  -- If we know the variable, we return its dependencies. 
  -- Otherwise we return nothing (since it was not found with freeVars)
  -- This can happen in regards to type variables such as i32
  -- or core Futhark functions such as map
  pure $
    case M.lookup vn env of
      Just x -> x
      Nothing -> DepVal mempty
      -- Alternatively: failure $ "Unknown variable: " <> (show vn) 
      -- Or: DepVal $ idsSingle vn


innerDepsExtend :: (StackTrace, VName, DepVal) -> InnerDepVals -> InnerDepVals
innerDepsExtend (st, vn, d) (Env env) = Env $ M.insert (addToStack vn st) d env
 
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

-- A semi-weird semi group. Used when performing union on environments 
instance Semigroup StackTrace where
  CallStack x <> CallStack y =
    if length x > length y
      then CallStack x
      else CallStack y 

instance Monoid StackTrace where
  mempty = emptyStack


idsSingle :: VName -> Ids
idsSingle v = Ids [v]

idsWithout :: VName -> Ids -> Ids
idsWithout x (Ids xs) = Ids $ filter (/=x) xs

mergeDepVals :: [Deps] -> Deps
mergeDepVals dps = foldr (<>) mempty dps 

-- | Extracting pure identifiers from DepVal
depValDeps :: DepVal -> InterpretM Deps
depValDeps (DepVal x) = pure x
depValDeps (DepGroup _ x) = do
  dps <- mapM (depValDeps . snd) $ TPL.sortFields x
  pure $ mergeDepVals dps
depValDeps (DepFun _ _ lst eb) = do
  d1 <- depsExpBase eb
  d2 <- depValDeps d1
  pure $ foldr idsWithout d2 $ concat $ map nestedNameDeps lst
  where nestedNameDeps :: NestedName -> [VName]
        nestedNameDeps WildcardName = mempty
        nestedNameDeps (Name vn) = [vn]
        nestedNameDeps (RecordName x) =
          concat $ map (nestedNameDeps . snd) $ M.toList x

-- | Joins two different sets of DepVal
-- Only records of equal length and fields can be joined
-- without collapsing to pure DepVal Deps
depValJoin :: DepVal -> DepVal -> InterpretM DepVal
depValJoin x@(DepGroup t r1) y@(DepGroup _ r2) =
  let (names1, tpl1) = unzip $ TPL.sortFields r1
      (names2, tpl2) = unzip $ TPL.sortFields r2
    in
      if names1 == names2 
        then do
          d_n <- zipWithM depValJoin tpl1 tpl2
          pure $ DepGroup t $ M.fromList $ zip names1 d_n
        else do
          dps1 <- depValDeps x
          dps2 <- depValDeps y
          pure $ DepVal $ dps1 <> dps2 
depValJoin x y = do
  dps1 <- depValDeps x
  dps2 <- depValDeps y
  pure $ DepVal $ dps1 <> dps2

-- | Injects dependencies into expressions
depValInj :: Deps -> DepVal -> InterpretM DepVal
depValInj x (DepVal y) = pure $ DepVal $ x <> y
depValInj x (DepGroup t r) = 
  let (names, tpl) = unzip $ TPL.sortFields r
    in do
      dps <- mapM (depValInj x) tpl
      pure $ DepGroup t $ M.fromList $ zip names dps
depValInj x v = do
  dps <- depValDeps v
  pure $ DepVal $ x <> dps

-- | Locates free variables in the body of ProgBase
-- OBS: Only handles the last progDecs currently
depsFreeVarsInProgBase :: ProgBase Info VName -> DepsEnv
depsFreeVarsInProgBase base =
  case last $ progDecs base of 
    ValDec valbind -> depsFreeVarsInExpBase $ valBindBody valbind
    _ -> mempty -- Should not return mempty

-- | Dependencies in ExpBase 
depsFreeVarsInExpBase :: ExpBase Info VName -> DepsEnv
depsFreeVarsInExpBase eb =
  Env $ M.fromList $ map (\x -> (x, DepVal mempty)) $ freeVarsList eb

-- | ExpBase to list of free variables in the form of VName's
freeVarsList :: ExpBase Info VName -> [VName]
freeVarsList eb = S.toList $ FV.fvVars $ freeInExp eb

-- | Converts pattern bases to pure NestedNames

extractPatBaseName :: PatBase Info VName t -> NestedName
extractPatBaseName (TuplePat pb_n _) =
  RecordName $ TPL.tupleFields $ map extractPatBaseName pb_n
extractPatBaseName (RecordPat npb_n _) =
  RecordName $ M.fromList $ map (\(L _ x, y) -> (x, extractPatBaseName y)) npb_n
extractPatBaseName (PatParens pb _) = extractPatBaseName pb
extractPatBaseName (Id vn _ _) = Name vn
extractPatBaseName (Wildcard _ _) = WildcardName
extractPatBaseName (PatAscription pb _ _) = extractPatBaseName pb
extractPatBaseName (PatLit _ _ _) = WildcardName
extractPatBaseName (PatConstr _ _ pb_n _) =
  -- This might not be correct:
  RecordName $ TPL.tupleFields $ map extractPatBaseName pb_n
extractPatBaseName (PatAttr _ pb _) = extractPatBaseName pb

-- | Used in LetFun to inject the parameter names into the set of dependencies
-- This is so f x = x + a evaluates to 'f' depending on x and a
-- instead of just resorting to a base case
-- which also catches "+" as a free variable which is annoying
injectNestedNames :: [NestedName] -> DepVal -> InterpretM DepVal
injectNestedNames names dv =
    foldM injectNestedNames' dv names 
    where injectNestedNames' :: DepVal -> NestedName -> InterpretM DepVal
          injectNestedNames' dv'@(DepVal d') name =
            case name of
              (Name vn) -> pure $ DepVal $ Ids [vn] <> d'
              (RecordName rcrd) -> do
                foldM injectNestedNames' dv' $ map snd $ M.toList rcrd
              WildcardName -> pure dv'
          injectNestedNames' (DepGroup t d_n) name =
            let (names', tpl) = unzip $ TPL.sortFields d_n
              in do
                d_n' <- mapM (\d' -> injectNestedNames' d' name) tpl
                pure $ DepGroup t $ M.fromList $ zip names' d_n'
          injectNestedNames' fun name = do
            d' <- depValDeps fun
            injectNestedNames' (DepVal d') name

-- | Converts nested names to pure DepsEnv's, should be used with care
nestedNamesToSelfEnv :: NestedName -> (DepsEnv, StackTrace)
nestedNamesToSelfEnv (Name vn) =
  (Env $ M.singleton vn $ DepVal $ idsSingle vn, emptyStack)
nestedNamesToSelfEnv (RecordName nv_n) =
  foldMap (nestedNamesToSelfEnv . snd) $ M.toList nv_n
nestedNamesToSelfEnv WildcardName = mempty

-- | Finds dependencies in declaration bases
depsDecBase :: DecBase Info VName -> InterpretM DepVal
depsDecBase (ValDec bindings) = do
  env <- askEnv
  let env' = foldMap (nestedNamesToSelfEnv . extractPatBaseName) $ 
              valBindParams bindings
    in localEnv (const $ env' <> env) $ depsExpBase $ valBindBody bindings
depsDecBase (TypeDec _) = failure "Does not support analysis of TypeDec"
depsDecBase (ModTypeDec _) = failure "Does not support analysis of ModTypeDec"
depsDecBase (ModDec _) = failure "Does not support analysis of ModDec"
depsDecBase (OpenDec _ _) = failure "Does not support analysis of OpenDec"
depsDecBase (LocalDec db _) = depsDecBase db 
depsDecBase (ImportDec _ _ _) = failure "Does not support analysis of ImportDec"

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
  depValJoin d1 d2
depsExpBase (TupLit ebn _) = do
  d_n <- mapM depsExpBase ebn
  pure $ DepGroup DepTuple $ TPL.tupleFields d_n
depsExpBase (RecordLit fb_n _) = do
  d_n <- mapM depsFieldBase fb_n
  pure $
    DepGroup DepRecord $ M.fromList $ zip (map extractFBName fb_n) d_n
  where extractFBName :: FieldBase Info VName -> Name
        extractFBName (RecordFieldExplicit (L _ name) _ _) = name
        extractFBName (RecordFieldImplicit (L _ (VName name _)) _ _) = name
depsExpBase (ArrayLit eb_n _ _) = do
  d_n <- mapM depsExpBase eb_n
  foldM depValJoin (DepVal mempty) d_n
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
            Nothing -> failure $
                        "Projection of tuple/record out of bounds with name " <>
                          show names
    _ -> failure "Tried to project a non-tuple/record"
depsExpBase (Negate eb _) = depsExpBase eb
depsExpBase (Not eb _) = depsExpBase eb
depsExpBase (Assert eb1 eb2 _ _) = do
  d1 <- depsExpBase eb1
  d2 <- depsExpBase eb2
  depValJoin d1 d2
depsExpBase (Constr _ eb_n _ _) = do
  d_n <- mapM depsExpBase eb_n
  foldM depValJoin (DepVal mempty) d_n
depsExpBase (Update eb1 sb eb2 _) = do
  d1 <- depsExpBase eb1
  d2 <- depsExpBase eb2
  d3 <- depValJoin d1 d2
  d_n <- depsSliceBase sb
  foldM depValJoin d3 d_n
depsExpBase (RecordUpdate eb1 n_n eb2 _ _) = do
  d1 <- depsExpBase eb1
  d2 <- depsExpBase eb2
  rcrdUpdate d1 d2 $ length n_n
  where rcrdUpdate :: DepVal -> DepVal -> Int -> InterpretM DepVal
        rcrdUpdate (DepGroup t rcrd) d' 1 | isJust $ M.lookup (head n_n) rcrd =
          pure $ DepGroup t $ M.update (\_ -> Just d') (head n_n) rcrd
        rcrdUpdate (DepFun _ _ _ body) d' 1 = do
          d3 <- depsExpBase body
          rcrdUpdate d3 d' 1 
          {- The above is if the record is in fact a function without arguments
            If the function has arguments, it becomes an AppExp containing a
            RecordUpdate instead, which is why this (^) is correct even though
            it seems odd. -}
        rcrdUpdate d3 d' _ = depValJoin d3 d' 
depsExpBase (OpSection qn _ _) = do
  env <- askEnv
  envLookup (qualLeaf qn) env
depsExpBase (OpSectionLeft qn _ eb _ _ _) = do
  env <- askEnv
  d0 <- envLookup (qualLeaf qn) env
  d1 <- depsExpBase eb
  depValJoin d0 d1
depsExpBase (OpSectionRight qn _ eb _ _ _) = do
  env <- askEnv
  d0 <- envLookup (qualLeaf qn) env
  d1 <- depsExpBase eb
  depValJoin d0 d1
depsExpBase (ProjectSection _ _ _) = pure $ DepVal mempty
depsExpBase (IndexSection sb _ _) = do
  d_n <- depsSliceBase sb
  foldM depValJoin (DepVal mempty) d_n
depsExpBase (Ascript eb _ _) = depsExpBase eb
depsExpBase (Coerce eb _ _ _) = depsExpBase eb 
depsExpBase (Lambda pb_n eb _ _ _) = do
  env <- askEnv
  let names = map extractPatBaseName pb_n
    in pure $ DepFun Nothing (fst env) names eb
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
    DepFun maybe_vn env' n_n body -> do
      env <- askEnv
      fun_env <-
        case foldr envUnionError (Right (env', emptyStack)) $
              zipWith depsEnvSingle (map Just n_n) d_n of
          Left e -> failure e
          Right e -> pure e 
      case (maybe_vn, snd env) of
        (Just vn, st) -> localEnv (const (fst fun_env, addToStack vn st)) $
                            depsExpBase body
        (Nothing, _) -> localEnv (const fun_env) $ depsExpBase body
    d2 -> foldM depValJoin d2 d_n
depsAppExpBase (Range eb1 maybe_eb2 inclusive_eb3 _) = do
  d1 <- depsExpBase eb1
  d2 <- maybe (pure $ DepVal mempty) depsExpBase maybe_eb2
  d3 <-
    case inclusive_eb3 of
      (DownToExclusive eb3) -> depsExpBase eb3
      (ToInclusive eb3) -> depsExpBase eb3
      (UpToExclusive eb3) -> depsExpBase eb3
  d4 <- depValJoin d1 d2
  depValJoin d3 d4
depsAppExpBase (LetPat _ pb eb1 eb2 _) = do
  d1 <- depsExpBase eb1
  env <- askEnv
  let name = extractPatBaseName pb
    in do
      logDep (snd env) d1 name 
      env' <- case depsEnvExtend (Just name) d1 env of
                (Left e) -> failure e
                (Right e) -> pure e
      localEnv (const env') $ depsExpBase eb2
depsAppExpBase (LetFun vn (_, pb_n, _, _, eb1) eb2 _ ) = do
  env <- askEnv
  let names = map extractPatBaseName pb_n
      fun = DepFun (Just vn) (fst env) names eb1
    in do
      d1 <- depsExpBase eb1
      d2 <- injectNestedNames names d1
      logDep (snd env) d2 $ Name vn
      env' <- pure $ depsEnvExtendPure vn fun env
      localEnv (const env') $ depsExpBase eb2
depsAppExpBase (If eb1 eb2 eb3 _) = do
  d1 <- depsExpBase eb1
  d2 <- depsExpBase eb2
  d3 <- depsExpBase eb3
  d4 <- depValJoin d2 d3
  d5 <- depValDeps d1
  depValInj d5 d4
depsAppExpBase (Loop _ pb lib lfb eb _) = 
  let vn = extractPatBaseName pb
    in do
      d1 <- case lib of
        (LoopInitExplicit eb') -> depsExpBase eb'
        (LoopInitImplicit (Info eb')) -> depsExpBase eb'
      env <- askEnv
      loop_env <- case depsEnvExtend (Just vn) d1 env of
        Right e -> pure e
        Left e -> failure e
      case lfb of
        For ib' eb' -> do
          d2 <- localEnv (const loop_env) $ depsExpBase eb'
          d3 <- loop vn (Just $ Name $ identName ib') d1
          d4 <- depValDeps d2
          depValInj d4 d3
        ForIn pb' eb' ->
          let vn' = Just $ extractPatBaseName pb'
            in do
              d2 <- localEnv (const loop_env) $ depsExpBase eb'
              d3 <- loop vn vn' d1
              d4 <- depValDeps d2
              depValInj d4 d3
        While eb' -> do
          d2 <- localEnv (const loop_env) $ depsExpBase eb'
          d3 <- loop vn Nothing d1
          d4 <- depValDeps d2
          depValInj d4 d3
      where loop :: NestedName -> Maybe NestedName -> DepVal -> InterpretM DepVal
            loop p i ld = do
              env  <- askEnv
              env' <- case (depsEnvSingle i (DepVal mempty)
                           ,depsEnvSingle (Just p) ld) of
                        (Left e, _) -> failure e
                        (_, Left e) -> failure e
                        (Right env1, Right env2) -> pure $ env2 <> env1 <> env
              ld' <- localEnv (const env') $ depsExpBase eb
              if ld == ld'
                then pure ld'
                else do
                  d' <- depValJoin ld ld' 
                  loop p i d'
depsAppExpBase (BinOp qn _ eb1 eb2 _) = do
  env <- askEnv
  d0 <- envLookup (qualLeaf $ fst qn) env
  d1 <- depsExpBase $ fst eb1
  d2 <- depsExpBase $ fst eb2
  d3 <- depValJoin d0 d1
  depValJoin d2 d3
depsAppExpBase (LetWith ib1 ib2 sb eb1 eb2 _) = do
  d_n <- depsSliceBase sb
  d1 <- depsExpBase eb1
  -- We could log the new array that is created.
  -- It depends on all the values of the first expression base but also
  -- indirectly on all the dependencies of the consumed array
  env <- askEnv
  d2 <- envLookup (identName ib2) env
  d3 <- depValJoin d1 d2
  logDep (snd env) d3 $ Name $ identName ib1
  env' <- pure $ depsEnvExtendPure (identName ib1) d1 env
  d4 <- mapM depValDeps d_n
  res <- localEnv (const env') $ depsExpBase eb2
  depValInj (mergeDepVals d4) res
depsAppExpBase (Index eb sb _) = do
  d <- depsExpBase eb 
  d_n <- depsSliceBase sb
  foldM depValJoin d d_n 
depsAppExpBase (Match eb ne_cb _) = do
  d1 <- depsExpBase eb
  d2 <- depValDeps d1
  d_n <- mapM depsCaseBase $ NE.toList ne_cb
  d_n' <- mapM (depValInj d2) d_n
  foldM depValJoin (DepVal mempty) d_n'

-- | Finds dependencies in case bases
depsCaseBase :: CaseBase Info VName -> InterpretM DepVal
depsCaseBase (CasePat _ eb _) = depsExpBase eb

-- | Finds dependencies in dimension index bases
depsDimIndexBase :: DimIndexBase Info VName -> InterpretM DepVal
depsDimIndexBase (DimFix eb) = depsExpBase eb
depsDimIndexBase (DimSlice maybe_eb1 maybe_eb2 maybe_eb3) = do
  d1 <- maybe (pure $ DepVal mempty) depsExpBase maybe_eb1
  d2 <- maybe (pure $ DepVal mempty) depsExpBase maybe_eb2
  d3 <- maybe (pure $ DepVal mempty) depsExpBase maybe_eb3
  d4 <- depValJoin d1 d2
  depValJoin d3 d4

-- | Finds dependencies in slice bases
depsSliceBase :: SliceBase Info VName -> InterpretM [DepVal]
depsSliceBase = mapM depsDimIndexBase

-- | Recursive executer of evaluation
interpretDepM :: (DepsEnv, StackTrace)
              -> InterpretM DepVal
              -> (Either Error DepVal, InnerDepVals)
interpretDepM _ (Pure x) = (Right x, Env M.empty)
interpretDepM env (Free (ReadOp k)) = interpretDepM env $ k env
interpretDepM env (Free (LogOp d1 x)) =
  let (y, d2) = interpretDepM env x
    in (y, innerDepsExtend d1 d2)
interpretDepM _ (Free (ErrorOp e)) = (Left e, Env M.empty)

-- | Logs dependencies
logDep :: StackTrace -> DepVal -> NestedName -> InterpretM ()
logDep st d (Name vn) = Free $ LogOp (st, vn, d) $ pure () 
logDep st (DepGroup _ r1) (RecordName r2) =
  let (_, tpl1) = unzip $ TPL.sortFields r1
      (_, tpl2) = unzip $ TPL.sortFields r2
    in do
      _ <- zipWithM (logDep st) tpl1 tpl2
      pure ()
logDep _ _ WildcardName = pure ()
logDep _ a b = failure $ "Failed to log an inner dependence between " <> 
                            show b <> "\tand\t" <> show a 

-- Finds the relation between the name and the explicit ExpBase in a DecBase
bindingInDecBase :: DepsEnv -> DecBase Info VName -> BoundDepVal
bindingInDecBase env (ValDec bind) = -- OBS
  let vn = valBindName bind
      fun = DepFun (Just vn) env (map extractPatBaseName $ valBindParams bind) $
              valBindBody bind
    in Depends vn fun
bindingInDecBase env (LocalDec db _) = bindingInDecBase env db 
bindingInDecBase _ _ = None Nothing

-- | Interpretation function for dependencies
deps :: DepsEnv -> Prog -> [Either Error (BoundDepVal, InnerDepVals)]
deps env prog = 
  -- Finds all the bindings on "program base" level, e.g. the main script level
  let bindings = map (bindingInDecBase env) $ progDecs prog 
    in map deps' $ zip bindings $ progDecs prog
    where deps' :: (BoundDepVal, DecBase Info VName) -> Either Error (BoundDepVal, InnerDepVals)
          deps' (Depends vn' _, db) = 
            case (interpretDepM (env, CallStack [vn']) $ depsDecBase db) of
              (Right d1, d2) -> Right (Depends vn' d1, d2)
              (Left e, _) -> Left $ "In function: " <> show vn' <> " " <> e
          deps' (_, db) = 
            case (interpretDepM (env, emptyStack) $ depsDecBase db) of
              (Right d1, d2) -> Right (None (Just d1), d2)
              (Left e, _) -> Left e

-- | A printer for printing a pretty string
prettyPrinter :: Either Error (BoundDepVal, InnerDepVals) -> String -> String
prettyPrinter (Right (bound, Env d_n)) acc =
  "\n\ESC[0mFunction: \ESC[95m" ++ show bound ++
  "\n\ESC[0m\tInner dependencies: \ESC[36m" ++ 
  (foldr (\(k, a) x -> x ++ "\n\t\t" ++ show k ++ " depends on " ++ show a) "" $ M.toList d_n)
  ++ "\n\ESC[0m" ++ acc 
prettyPrinter (Left e) acc =
  "\n\ESC[31mError in dependency interpreter in function: \n\ESC[95m"
  ++ show e ++ "\n\ESC[0m" ++ acc

-- Inserts top level functions of the program base into the provided env.  
joinTopLevelDefs :: DepsEnv -> Prog -> DepsEnv
joinTopLevelDefs env prog =
  foldr (\dec env' -> joinTopLevelDefs' (bindingInDecBase env' dec) env') env $
      progDecs prog  
    where joinTopLevelDefs' :: BoundDepVal -> DepsEnv -> DepsEnv
          joinTopLevelDefs' (Depends vn d) env' =
            fst $ depsEnvExtendPure vn d (env', emptyStack)
          joinTopLevelDefs' _ env' = env'

-- | Folds all the dependencies with a given printer over all program bases 
depsFolder :: forall a . ([Either Error (BoundDepVal, InnerDepVals)] -> a -> a)
           -> a -> [Prog] -> a
depsFolder printer base progs =
  snd $ foldr depsFolder' (mempty, base) progs
        where depsFolder' :: Prog -> (DepsEnv, a) -> (DepsEnv, a) 
              depsFolder' prog (env, s) =
                let env' = joinTopLevelDefs env prog
                    either_d = deps (env' <> depsFreeVarsInProgBase prog) prog
                  -- Extending the top level definitions for functions
                  in (env', printer either_d s)

-- | Finds dependencies in a program
runDeps :: [Prog] -> String
runDeps progs = depsFolder (\d s -> foldr prettyPrinter s d) "" progs

-- | Finds dependencies in a program (outputs more readable data)
testDeps :: [Prog] -> [[Either Error (BoundDepVal, InnerDepVals)]]
testDeps progs = depsFolder (\d s -> [d] ++ s) [] progs
