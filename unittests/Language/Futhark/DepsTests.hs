module Language.Futhark.DepsTests (tests) where

import Language.Futhark.Deps
import Test.Tasty
import Test.Tasty.HUnit
import Language.Futhark
import Data.Map qualified as M
import Futhark.Compiler
import System.IO
import System.IO.Temp
import Data.List (sort, sortOn)

type Error = String

-- | Data type for testing
-- Exists so that we may avoid comparing actual VNames and instead just strings
-- since we can prove that all variables are unique in our tests
data DepValTest
  = DepValT [String]
  | DepGroupT [(String, DepValTest)]
  | DepFunT [([String], DepValTest)] [NestedNameT]
  deriving (Eq, Show)

data NestedNameT
  = NameT String
  | NestedNameT [(String, NestedNameT)]
  deriving (Eq, Show)

-- | Converts VName to string
stripVName :: VName -> String
stripVName (VName x _) = nameToString x

-- | Converts nested names to its testing counterpart
stripNestedName :: NestedName -> NestedNameT
stripNestedName (Name vn) = NameT $ stripVName vn
stripNestedName (RecordName rcrd) =
  NestedNameT $ map (\(x, y) -> (nameToString x, stripNestedName y)) $ sortOn fst $ M.toList rcrd
stripNestedName WildcardName = NameT "" 

-- | Converts InnerDepVals into its testing counterpart
stripEnv :: DepsEnv -> [([String], DepValTest)]
stripEnv (Env env) = sortOn fst $ map (\(x, y) -> ([stripVName x], stripDepVal y)) $ M.toList env

-- | Converts InnerDepVals into its testing counterpart
stripInner :: InnerDepVals -> [([String], DepValTest)]
stripInner (Env inner) = sortOn fst $ map (\(CallStack x, y) -> (map stripVName x, stripDepVal y)) $ M.toList inner

-- | Converts DepVal into its testing counterpart
stripDepVal :: DepVal -> DepValTest
stripDepVal (DepVal (Ids deps)) =
  DepValT $ sort $ map stripVName deps
stripDepVal (DepGroup _ rcrd) =
  DepGroupT $ sortOn fst $ map (\(x, y) -> (nameToString x, stripDepVal y)) $ M.toList rcrd
stripDepVal (DepFun _ env names _) = DepFunT (stripEnv env) $ map stripNestedName names

-- | Transforms general results 
transformDeps :: [(Either Error (BoundDepVal, InnerDepVals))] -> [(Either Error ([String], DepValTest))]
transformDeps [] = []
transformDeps ((Right (Depends (VName name _) d, inner)):t) =
  [Right ([nameToString name], stripDepVal d)] ++ (map Right $ stripInner inner) ++ (transformDeps t)
transformDeps ((Right (None (Just d), inner)):t) =
  [Right ([""], stripDepVal d)] ++ (map Right $ stripInner inner) ++ (transformDeps t)
transformDeps ((Right (None Nothing, inner)):t) =
  (map Right $ stripInner inner) ++ (transformDeps t)
transformDeps ((Left e):t) = [Left e] ++ (transformDeps t)

-- | Tests a program written in a string
testWithTempFile :: String -> [(Either Error ([String], DepValTest))] -> FilePath -> Handle -> IO ()
testWithTempFile content correct file h = do
    hPutStr h content
    hClose h
    (_, imports, _) <- readProgramOrDie file
    -- We only observe the tail of the last output since this corresponds to the
    -- dependencies of the actual script (without OpenDec)
    let res = tail $ last $ testDeps $ map (fileProg . snd) imports
      in correct @=? transformDeps res

-- | Executes a unit test
unitDepTest :: String -> [(Either Error ([String], DepValTest))] -> IO () 
unitDepTest prog_str correct =
  withSystemTempFile "test.fut" $ testWithTempFile prog_str correct

tests :: TestTree
tests =
  testGroup
    "Dependencies"
    [ 
      -- ======================= Larger algorithms ============================= 
      -- (Taken from https://futhark-lang.org/examples.html)

      -- =============== Odd-balls/edge cases/comprised tests: =================

      testCase "Inner empty binding" $
        unitDepTest "def f = let a = 3 in a"
          [Right (["f"], DepValT [])
          ,Right (["f","a"], DepValT [])],

      testCase "Inner tuple binding" $
        unitDepTest "def f2 a = (a, 42) \
                    \\ndef f1 arg = f2 arg"
          [Right (["f2"], DepGroupT [("0", DepValT ["a"]), ("1", DepValT [])])
          ,Right (["f1"], DepGroupT [("0", DepValT ["arg"]), ("1", DepValT [])])],

      testCase "Conditional tuple in function call" $
        unitDepTest "def f2 a b = \
                      \\n   let c = if b > 0 \
                      \\n       then (0, a) \
                      \\n       else (b, b) \
                      \\n   in c \
                      \\ndef f1 arg = f2 arg 6"
          [Right (["f2"],DepGroupT [("0",DepValT ["b"]),("1",DepValT ["a","b"])])
          ,Right (["f2", "c"], DepGroupT [("0",DepValT ["b"]),("1",DepValT ["a","b"])])
          ,Right (["f1"],DepGroupT [("0",DepValT []),("1",DepValT ["arg"])])
          ,Right (["f1", "f2", "c"], DepGroupT [("0",DepValT []),("1",DepValT ["arg"])])],
          -- OBS, logs c again since it logged when analyzing f1

      testCase "Fixed point iteration in loop" $
        unitDepTest "def f (x0 : i32) (x1 : i32) (x2 : i32) (n : i32) = \
                     \\n  let x = \
                     \\n      loop acc = (x0, x1, x2) for i < n do \
                     \\n          (acc.1, acc.2, acc.0) \
                     \\n  in x.0"
          [Right (["f"],DepValT ["n", "x0", "x1", "x2"])
          ,Right (["f", "x"],DepGroupT [("0", DepValT ["n", "x0", "x1", "x2"]),
                                 ("1", DepValT ["n", "x0", "x1", "x2"]),
                                 ("2", DepValT ["n", "x0", "x1", "x2"])])],
                                 
      testCase "Free variables in core Futhark functions" $ 
        unitDepTest "def f1 (y : i64) (xs : [4]i64) = \
                     \\n  let f2 x = i64.sum (iota (x + y)) \
                     \\n  in map f2 xs"
          [Right (["f1"],DepValT ["xs","y"])
          ,Right (["f1", "f2"],DepValT ["+","iota","sum", "x","y"])],
          -- Currently i64.sum is not supported (because it is under TypeDec)
          -- which results in a base-case which is simply the free variables of the expression

      testCase "Records in conditional" $
        unitDepTest "def a_record (a : i32) = \
                     \\n  {foo = 0, bar = true} with foo = a \
                     \\ndef f (c : bool) (i : i32) = \
                     \\n    if c \
                     \\n        then a_record i \
                     \\n        else {foo = 2, bar = c}"
          [Right (["a_record"],DepGroupT [("bar",DepValT []),("foo",DepValT ["a"])])
          ,Right (["f"], DepGroupT [("bar", DepValT ["c"]), ("foo", DepValT ["c", "i"])])],

      testCase "Pattern matching" $
        unitDepTest "type bool_or_tpl = #bool bool | #tpl (i32, i32) \
                     \\ndef f (a : bool_or_tpl) (b : i32) (c : i32) : bool_or_tpl = \
                     \\n  match a \
                     \\n  case #bool x -> #bool x \
                     \\n  case #tpl (y, z) -> #tpl (y, c + b)"
          [Left "Does not support analysis of TypeDec"
          ,Right (["f"],DepValT ["a", "b", "c"])],

      -- ========================== ExpBase tests: =============================

      testCase "TupLit" $
        unitDepTest "def f (a : i32) (b : i32) (c : i32) = (a + b, (c, b + 10), 0)"
          [Right (["f"], DepGroupT [
                        ("0", DepValT ["a", "b"]),
                        ("1", DepGroupT [
                              ("0", DepValT ["c"]),
                              ("1", DepValT ["b"])]),
                        ("2", DepValT [])])],

      testCase "RecordLit" $
        unitDepTest "def f (a : i32) (b : i32) (c : i32) = {foo = a + b, bar = (c, b + 10)}"
          [Right (["f"], DepGroupT [
                        ("bar", DepGroupT [
                              ("0", DepValT ["c"]),
                              ("1", DepValT ["b"])]),
                        ("foo", DepValT ["a", "b"])])],

      testCase "ArrayLit" $
        unitDepTest "def f (a : i32) (b : i32) (c : i32) = [a, 0, b, 1, 24, c]"
          [Right (["f"], DepValT ["a", "b", "c"])],

      testCase "Update" $
        unitDepTest "def f (a : i64) (b : i64) (c : i64) = [b, 0, a, 1, 24][c:]"
          [Right (["f"], DepValT ["a", "b", "c"])],

      testCase "RecordUpdate 1" $
        unitDepTest "def rcrd = {foo = 0, bar = (1, 2)} \
                     \\ndef f (a : i32) (b : i32) (c : i32) = \
                     \\n  rcrd with bar = (a, b) "
          [Right (["rcrd"],DepGroupT [
                            ("bar",DepGroupT [
                                ("0",DepValT []),
                                ("1",DepValT [])]),
                            ("foo",DepValT [])])
          ,Right (["f"],DepGroupT [
                            ("bar",DepGroupT [
                                ("0",DepValT ["a"]),
                                ("1",DepValT ["b"])]),
                            ("foo",DepValT [])])],
      
      testCase "RecordUpdate 2" $
        unitDepTest "def rcrd (c : i32) = {foo = c, bar = (1, 2)} \
                     \\ndef f (a : i32) (b : i32) (c : i32) = \
                     \\n  rcrd c with bar = (a, b) "
          [Right (["rcrd"],DepGroupT [
                              ("bar",DepGroupT [
                                  ("0",DepValT []),
                                  ("1",DepValT [])]),
                              ("foo",DepValT ["c"])])
          ,Right (["f"],DepGroupT [
                              ("bar",DepGroupT [
                                  ("0",DepValT ["a"]),
                                  ("1",DepValT ["b"])]),
                                  ("foo",DepValT ["c"])])],

      testCase "OpSections" $
        unitDepTest "def f2 (x : i32) (y : i32) = x + y \
                     \\ndef f1 (a : i32) (b : i32) (c : i32) = (f2 a) (b `f2` c)"
          [Right (["f2"], DepValT ["x", "y"])
          ,Right (["f1"], DepValT ["a", "b", "c"])],

      -- ========================== FieldBase tests: ===========================
        
      testCase "RecordFieldExplicit" $
        unitDepTest "type p = {x : i32, y : i32}\
                     \\ndef f2 (x' : i32) (y' : i32) : p = {x = x' + y', y = y'} \
                     \\ndef f1 (a : i32) (b : i32) = \
                     \\n  let {x, y} = f2 a b \
                     \\n  in x + y"
          [Left "Does not support analysis of TypeDec"
          ,Right (["f2"], DepGroupT [("x", DepValT["x'","y'"]), ("y", DepValT["y'"])])
          ,Right (["f1"], DepValT ["a", "b"])
          ,Right (["f1","x"],DepValT ["a", "b"])
          ,Right (["f1","y"],DepValT ["b"])],

      testCase "RecordFieldImplicit" $
        unitDepTest "type p = {x : i32, y : i32}\
                     \\ndef f2 (x' : i32) (y' : i32) : p = {x = x' + y', y = y'} \
                     \\ndef f1 (a : i32) (b : i32) = \
                     \\n  let {x = x, y = y} = f2 a b \
                     \\n  in x + y"
          [Left "Does not support analysis of TypeDec"
          ,Right (["f2"], DepGroupT [("x", DepValT["x'", "y'"]), ("y", DepValT["y'"])])
          ,Right (["f1"], DepValT ["a", "b"])
          ,Right (["f1","x"],DepValT ["a", "b"])
          ,Right (["f1","y"],DepValT ["b"])],

      -- ========================== AppExpBase tests: ==========================

          -- Missing apply (both ways)

      testCase "Ranges" $
        unitDepTest "def f (a : i32) (b : i32) (c : i32) = a..b...c"
          [Right (["f"], DepValT ["a", "b", "c"])],

      testCase "LetPat 1 (pure)" $
        unitDepTest "def f (b : i32) = \
                     \\n  let a = b \
                     \\n  in b "
          [Right (["f"], DepValT ["b"])
          ,Right (["f", "a"], DepValT ["b"])],

      testCase "LetPat 2 (lambda)" $
        unitDepTest "def f (b : i32) = \
                     \\n  let a = \\x -> x \
                     \\n  in a b"
          [Right (["f"], DepValT ["b"])
          ,Right (["f","a"], DepFunT [(["b"], DepValT ["b"]),(["f"], DepFunT [] [NameT "b"])] [NameT "x"])],

      testCase "LetPat 3 (function)" $
        unitDepTest "def f2 (x : i32) =\
                     \\n  let y = x \ 
                     \\n  in y \
                     \\ndef f1 (b : i32) = \
                     \\n  let a = f2 \
                     \\n  in a b"
          [Right (["f2"], DepValT ["x"])
          ,Right (["f2","y"], DepValT ["x"])
          ,Right (["f1"], DepValT ["b"])
          ,Right (["f1","a"], DepFunT [(["f1"], DepFunT [] [NameT "b"])] [NameT "x"])
          ,Right (["f1","f2","y"], DepValT ["b"])]
          -- A "fun" thing to note here is that f2 does not store "b" in its domain of the environment
          -- but in the previous test (LetPat 2 lambda), "b" is a part of the domain
          -- This is because functions are statically typed


      -- ========================== CaseBase tests: ============================

      -- ========================== DimIndexBase tests: ========================

    ]