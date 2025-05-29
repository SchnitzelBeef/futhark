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
data DepValTest
  = DepValT [String]
  | DepGroupT [(String, DepValTest)]
  | DepFunT [(String, DepValTest)] [NestedName]
  deriving (Eq, Show)

-- | Converts DepVal into its testing counterpart
stripDepVal :: DepVal -> DepValTest
stripDepVal (DepVal (Ids deps)) = DepValT $ sort $ map (\(VName x _) -> nameToString x) deps
stripDepVal (DepGroup _ rcrd) =
  DepGroupT $ sortOn fst $ map (\(x, y) -> (nameToString x, stripDepVal y)) $ M.toList rcrd
stripDepVal (DepFun env names _) = DepFunT (stripEnv env) names

-- | Converts InnerDepVals into its testing counterpart
stripEnv :: InnerDepVals -> [(String, DepValTest)]
stripEnv (Env deps) = sortOn fst $ map (\((VName x _), y) -> (nameToString x, stripDepVal y)) $ M.toList deps

-- | Transforms general results from 
transformDeps :: [(Either Error (BoundDepVal, InnerDepVals))] -> [(Either Error (String, DepValTest))]
transformDeps [] = []
transformDeps ((Right (Depends (VName name _) d, env)):t) =
  [Right (nameToString name, stripDepVal d)] ++ (map Right $ stripEnv env) ++ (transformDeps t)
transformDeps ((Right (None (Just d), env)):t) =
  [Right ("", stripDepVal d)] ++ (map Right $ stripEnv env) ++ (transformDeps t)
transformDeps ((Right (None Nothing, env)):t) =
  (map Right $ stripEnv env) ++ (transformDeps t)
transformDeps ((Left e):t) = [Left e] ++ (transformDeps t)

-- | Tests a program written in a string
testWithTempFile :: String -> [(Either Error (String, DepValTest))] -> FilePath -> Handle -> IO ()
testWithTempFile content correct file h = do
    hPutStr h content
    hClose h
    (_, imports, _) <- readProgramOrDie file
    let res = (testDeps . fileProg . snd . last) imports
      in correct @=? transformDeps res

-- | Executes a unit test
unitDepTest :: String -> [(Either Error (String, DepValTest))] -> IO () 
unitDepTest prog_str correct =
  withSystemTempFile "test.fut" $ testWithTempFile prog_str correct

tests :: TestTree
tests =
  testGroup
    "Dependencies"
    [ 
      testCase "Inner empty binding" $
        unitDepTest "def f = let a = 3 in a"
          [Left "Does not support analysis of OpenDec"
          ,Right ("f", DepValT [])
          ,Right ("a", DepValT [])],

      testCase "Inner tuple binding" $
        unitDepTest "def f2 a = (a, 42) \
                    \\ndef f1 arg = f2 arg"
          [Left "Does not support analysis of OpenDec",
          Right ("f2", DepGroupT [("0", DepValT ["a"]), ("1", DepValT [])]),
          Right ("f1", DepGroupT [("0", DepValT ["arg"]), ("1", DepValT [])])],

      testCase "Conditional tuple in function call" $
        unitDepTest "def f2 a b = \
                      \\n   let c = if b > 0 \
                      \\n       then (0, a) \
                      \\n       else (b, b) \
                      \\n   in c \
                      \\ndef f1 arg = f2 arg 6"
          [Left "Does not support analysis of OpenDec"
          ,Right ("f2",DepGroupT [("0",DepValT ["b"]),("1",DepValT ["a","b"])])
          ,Right ("c" ,DepGroupT [("0",DepValT ["b"]),("1",DepValT ["a","b"])])
          ,Right ("f1",DepGroupT [("0",DepValT []),("1",DepValT ["arg"])])
          ,Right ("c" ,DepGroupT [("0",DepValT []),("1",DepValT ["arg"])])],
          -- OBS, logs c again since it logged when analyzing f1

      testCase "Fixed point iteration in loop" $
        unitDepTest "def f (x0 : i32) (x1 : i32) (x2 : i32) (n : i32) = \
                     \\n  let x = \
                     \\n      loop acc = (x0, x1, x2) for i < n do \
                     \\n          (acc.1, acc.2, acc.0) \
                     \\n  in x.0"
          [Left "Does not support analysis of OpenDec"
          ,Right ("f",DepValT ["n", "x0", "x1", "x2"])
          ,Right ("x",DepGroupT [("0", DepValT ["n", "x0", "x1", "x2"]),
                                 ("1", DepValT ["n", "x0", "x1", "x2"]),
                                 ("2", DepValT ["n", "x0", "x1", "x2"])])],
                                 
      testCase "Free variables in core Futhark functions" $ 
        unitDepTest "def f1 (y : i64) (xs : [4]i64) = \
                     \\n  let f2 x = i64.sum (iota (x + y)) \
                     \\n  in map f2 xs"
          [Left "Does not support analysis of OpenDec"
          ,Right ("f1",DepValT ["+","iota","sum","xs","y"])
          ,Right ("f2",DepValT ["+","iota","sum","x","y"])],
          -- A lot of "extra" dependencies that does not actually exist are also logged since they are "free variables"
          -- Working on fixing this...

      testCase "Records" $
        unitDepTest "def a_record (a : i32) = \
                     \\n  {foo = 0, bar = true} with foo = a \
                     \\ndef f (c : bool) (i : i32) = \
                     \\n    if c \
                     \\n        then a_record i \
                     \\n        else {foo = 2, bar = c}"
          [Left "Does not support analysis of OpenDec"
          ,Right ("a_record",DepGroupT [("bar",DepValT []),("foo",DepValT ["a"])])
          ,Right ("f", DepGroupT [("bar", DepValT ["c"]), ("foo", DepValT ["c", "i"])])]

    ]