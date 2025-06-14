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
  = DepsT [String]
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
stripDepVal (Deps (Ids deps)) =
  DepsT $ sort $ map stripVName deps
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
      -- =============== Odd-balls/edge cases/comprised tests: =================

      testCase "Inner empty binding" $
        unitDepTest "def f = let a = 3 in a"
          [Right (["f"], DepsT [])
          ,Right (["f","a"], DepsT [])],

      testCase "Inner tuple binding" $
        unitDepTest "def f2 a = (a, 42) \
                    \\ndef f1 arg = f2 arg"
          [Right (["f2"], DepGroupT [("0", DepsT ["a"]), ("1", DepsT [])])
          ,Right (["f1"], DepGroupT [("0", DepsT ["arg"]), ("1", DepsT [])])],

      testCase "Conditional tuple in function call" $
        unitDepTest "def f2 a b = \
                      \\n   let c = if b > 0 \
                      \\n       then (0, a) \
                      \\n       else (b, b) \
                      \\n   in c \
                      \\ndef f1 arg = f2 arg 6"
          [Right (["f2"], DepGroupT [("0", DepsT ["b"]),("1", DepsT ["a","b"])])
          ,Right (["f2", "c"], DepGroupT [("0", DepsT ["b"]),("1", DepsT ["a","b"])])
          ,Right (["f1"], DepGroupT [("0", DepsT []),("1", DepsT ["arg"])])
          ,Right (["f1", "f2", "c"], DepGroupT [("0", DepsT []),("1", DepsT ["arg"])])],

      testCase "Fixed point iteration in loop" $
        unitDepTest "def f (x0 : i32) (x1 : i32) (x2 : i32) (n : i32) = \
                     \\n  let x = \
                     \\n      loop acc = (x0, x1, x2) for i < n do \
                     \\n          (acc.1, acc.2, acc.0) \
                     \\n  in x.0"
          [Right (["f"], DepsT ["n", "x0", "x1", "x2"])
          ,Right (["f", "x"], DepGroupT [("0", DepsT ["n", "x0", "x1", "x2"]),
                                 ("1", DepsT ["n", "x0", "x1", "x2"]),
                                 ("2", DepsT ["n", "x0", "x1", "x2"])])],
                                 
      testCase "Free variables in core Futhark functions" $ 
        unitDepTest "def f1 (y : i64) (xs : [4]i64) = \
                     \\n  let f2 x = i64.sum (iota (x + y)) \
                     \\n  in map f2 xs"
          [Right (["f1"], DepsT ["xs","y"])
          ,Right (["f1", "f2"], DepsT ["x","y"])],
          -- Currently i64.sum is not supported (because it is under TypeDec)
          -- which results in a base-case which is simply the free variables of the expression

      testCase "Records in conditional" $
        unitDepTest "def a_record (a : i32) = \
                     \\n  {foo = 0, bar = true} with foo = a \
                     \\ndef f (c : bool) (i : i32) = \
                     \\n    if c \
                     \\n        then a_record i \
                     \\n        else {foo = 2, bar = c}"
          [Right (["a_record"], DepGroupT [("bar", DepsT []),("foo", DepsT ["a"])])
          ,Right (["f"], DepGroupT [("bar", DepsT ["c"]), ("foo", DepsT ["c", "i"])])],

      -- Taken from https://futhark-lang.org/examples/binary-search.html
      testCase "Binary search" $
        unitDepTest "def binary_search [n] 't (lte: t -> t -> bool) (xs: [n]t) (x: t) : i64 = \
                     \\n  let (l, _) = \
                     \\n    loop (l, r) = (0, n-1) while l < r do \
                     \\n    let t = l + (r - l) / 2 \
                     \\n    in if x `lte` xs[t] \
                     \\n      then (l, t) \
                     \\n      else (t+1, r) \
                     \\n  in l"
          [Right (["binary_search"], DepsT ["lte","x","xs"])
          ,Right (["binary_search","l"], DepsT ["lte","x","xs"])
          ,Right (["binary_search","t"], DepsT [])],
          -- It could be argued that t depends on r in the above example 

      -- Taken from https://futhark-lang.org/examples/searching.html
      testCase "Searching" $
        unitDepTest "type found 'a = #found a | #not_found \
                     \\ndef find_elem 'a [n] (p: a -> bool) (as: [n]a) : found a = \
                     \\n  let tag x = if p x then #found x else #not_found \
                     \\n  let op x y = \
                     \\n    match (x,y) \
                     \\n    case (#found _, _) -> x \
                     \\n    case (_, #found _) -> y \
                     \\n    case _             -> x \
                     \\n  in reduce_comm op #not_found (map tag as)"
          [Left "Does not support analysis of TypeDec"
          ,Right (["find_elem"], DepsT ["as","p"])
          ,Right (["find_elem","op"], DepsT ["x","y"])
          ,Right (["find_elem","tag"], DepsT ["p","x"])],

      -- ========================== ExpBase tests: =============================

      testCase "TupLit" $
        unitDepTest "def f (a : i32) (b : i32) (c : i32) = (a + b, (c, b + 10), 0)"
          [Right (["f"], DepGroupT [
                        ("0", DepsT ["a", "b"]),
                        ("1", DepGroupT [
                              ("0", DepsT ["c"]),
                              ("1", DepsT ["b"])]),
                        ("2", DepsT [])])],

      testCase "RecordLit" $
        unitDepTest "def f (a : i32) (b : i32) (c : i32) = {foo = a + b, bar = (c, b + 10)}"
          [Right (["f"], DepGroupT [
                        ("bar", DepGroupT [
                              ("0", DepsT ["c"]),
                              ("1", DepsT ["b"])]),
                        ("foo", DepsT ["a", "b"])])],

      testCase "ArrayLit" $
        unitDepTest "def f (a : i32) (b : i32) (c : i32) = [a, 0, b, 1, 24, c]"
          [Right (["f"], DepsT ["a", "b", "c"])],

      -- Below example taken from https://futhark.readthedocs.io/en/latest/language-reference.html#in-place-updates
      testCase "Update" $
        unitDepTest "def modify (a: *[]i32) (i: i32) (x: i32): *[]i32 = \
                     \\n  a with [i] = a[i] + x"
          [Right (["modify"], DepsT ["a", "i", "x"])],

      testCase "RecordUpdate 1" $
        unitDepTest "def rcrd = {foo = 0, bar = (1, 2)} \
                     \\ndef f (a : i32) (b : i32) (c : i32) = \
                     \\n  rcrd with bar = (a, b) "
          [Right (["rcrd"], DepGroupT [
                            ("bar", DepGroupT [
                                ("0", DepsT []),
                                ("1", DepsT [])]),
                            ("foo", DepsT [])])
          ,Right (["f"], DepGroupT [
                            ("bar", DepGroupT [
                                ("0", DepsT ["a"]),
                                ("1", DepsT ["b"])]),
                            ("foo", DepsT [])])],
      
      testCase "RecordUpdate 2" $
        unitDepTest "def rcrd (c : i32) = {foo = c, bar = (1, 2)} \
                     \\ndef f (a : i32) (b : i32) (c : i32) = \
                     \\n  rcrd c with bar = (a, b) "
          [Right (["rcrd"], DepGroupT [
                              ("bar", DepGroupT [
                                  ("0", DepsT []),
                                  ("1", DepsT [])]),
                              ("foo", DepsT ["c"])])
          ,Right (["f"], DepGroupT [
                              ("bar", DepGroupT [
                                  ("0", DepsT ["a"]),
                                  ("1", DepsT ["b"])]),
                                  ("foo", DepsT ["c"])])],

      testCase "OpSections" $
        unitDepTest "def f2 (x : i32) (y : i32) = x + y \
                     \\ndef f1 (a : i32) (b : i32) (c : i32) = (f2 a) (b `f2` c)"
          [Right (["f2"], DepsT ["x", "y"])
          ,Right (["f1"], DepsT ["a", "b", "c"])],

      -- ========================== FieldBase tests: ===========================
        
      testCase "RecordFieldExplicit" $
        unitDepTest "type p = {x : i32, y : i32}\
                     \\ndef f2 (x' : i32) (y' : i32) : p = {x = x' + y', y = y'} \
                     \\ndef f1 (a : i32) (b : i32) = \
                     \\n  let {x, y} = f2 a b \
                     \\n  in x + y"
          [Left "Does not support analysis of TypeDec"
          ,Right (["f2"], DepGroupT [("x", DepsT["x'","y'"]), ("y", DepsT["y'"])])
          ,Right (["f1"], DepsT ["a", "b"])
          ,Right (["f1","x"], DepsT ["a", "b"])
          ,Right (["f1","y"], DepsT ["b"])],

      testCase "RecordFieldImplicit" $
        unitDepTest "type p = {x : i32, y : i32}\
                     \\ndef f2 (x' : i32) (y' : i32) : p = {x = x' + y', y = y'} \
                     \\ndef f1 (a : i32) (b : i32) = \
                     \\n  let {x = x, y = y} = f2 a b \
                     \\n  in x + y"
          [Left "Does not support analysis of TypeDec"
          ,Right (["f2"], DepGroupT [("x", DepsT["x'", "y'"]), ("y", DepsT["y'"])])
          ,Right (["f1"], DepsT ["a", "b"])
          ,Right (["f1","x"],DepsT ["a", "b"])
          ,Right (["f1","y"],DepsT ["b"])],

      -- ========================== AppExpBase tests: ==========================

      testCase "Ranges" $
        unitDepTest "def f (a : i32) (b : i32) (c : i32) = a..b...c"
          [Right (["f"], DepsT ["a", "b", "c"])],

      testCase "LetPat 1 (pure)" $
        unitDepTest "def f (b : i32) = \
                     \\n  let a = b \
                     \\n  in b "
          [Right (["f"], DepsT ["b"])
          ,Right (["f", "a"], DepsT ["b"])],

      testCase "LetPat 2 (lambda)" $
        unitDepTest "def f (b : i32) = \
                     \\n  let a = \\x -> x \
                     \\n  in a b"
          [Right (["f"], DepsT ["b"])
          ,Right (["f","a"], DepFunT [(["b"], DepsT ["b"]),(["f"], DepFunT [] [NameT "b"])] [NameT "x"])],

      testCase "LetPat 3 (function)" $
        unitDepTest "def f2 (x : i32) =\
                     \\n  let y = x \ 
                     \\n  in y \
                     \\ndef f1 (b : i32) = \
                     \\n  let a = f2 \
                     \\n  in a b"
          [Right (["f2"], DepsT ["x"])
          ,Right (["f2","y"], DepsT ["x"])
          ,Right (["f1"], DepsT ["b"])
          ,Right (["f1","a"], DepFunT [(["f1"], DepFunT [] [NameT "b"])] [NameT "x"])
          ,Right (["f1","f2","y"], DepsT ["b"])],
          -- A "fun" thing to note here is that f2 does not store "b" in its domain of the environment
          -- but in the previous test (LetPat 2 lambda), "b" is a part of the domain
          -- This is because functions are statically typed

      testCase "LetFun 1" $
        unitDepTest "def f (a : i32) (b : i32) = \
                     \\n  let f' x = x + b \
                     \\n  in f' a"
          [Right (["f"], DepsT ["a", "b"])
          ,Right (["f", "f'"], DepsT ["b", "x"])],

      testCase "LetFun 2" $
        unitDepTest "def f (a : i32) (b : i32) = \
                     \\n  let f' (x, y) = x + y \
                     \\n  in f' (a, b)"
          [Right (["f"], DepsT ["a", "b"])
          ,Right (["f", "f'"], DepsT ["x", "y"])],

      testCase "If 1 (inject into deps)" $
        unitDepTest "def f (a : i32) (b : i32) (c : bool) = \
                     \\n  if c \
                     \\n  then a   \
                     \\n  else b "
          [Right (["f"], DepsT ["a", "b", "c"])],

      testCase "If 2 (inject into tuple)" $
        unitDepTest "def f (a : i32) (b : i32) (c : bool) = \
                     \\n  if c \
                     \\n  then (a, 0)   \
                     \\n  else (1, b) "
          [Right (["f"], DepGroupT [("0", DepsT ["a", "c"]), ("1", DepsT ["b", "c"])])],

      testCase "Loop 1 (for) " $
        unitDepTest "def f (a : i32) (b : i32) (n : i32) = \
                     \\n  loop x = a for i < n do \
                     \\n    x + b "
          [Right (["f"], DepsT ["a", "b", "n"])],

      testCase "Loop 2 (for in) " $
        unitDepTest "def f (a : i32) (b : i32) (s : i32) = \
                     \\n  loop x = a for i in s...10 do \
                     \\n    x + b "
          [Right (["f"], DepsT ["a", "b", "s"])],

      testCase "Loop 3 (while) " $
        unitDepTest "def f (a : i32) (b : i32) (s : i32) = \
                     \\n  loop x = a while x < s do \
                     \\n    x + b "
          [Right (["f"], DepsT ["a", "b", "s"])],

      testCase "LetWith" $
        unitDepTest "def f (a: *[]i32) (i: i32) (x: i32): *[]i32 = \
                     \\n  let b = a with [i] = a[i] + x \
                     \\n  in b "
          [Right (["f"], DepsT ["a", "i", "x"])
          ,Right (["f", "b"], DepsT ["a", "i", "x"])],

      testCase "Index" $
        unitDepTest "def f (a : i64) (b : i64) (c : i64) = [b, 0, a, 1, 24][c:]"
          [Right (["f"], DepsT ["a", "b", "c"])],

      testCase "Match" $
        unitDepTest "type int_or_tpl = #int i32 | #tpl (i32, i32) \
                     \\ndef f (a : i32) (b : i32) (c : bool) : int_or_tpl= \
                     \\n  match c \
                     \\n  case true -> #int a \
                     \\n  case false -> #tpl (a, b) "
          [Left "Does not support analysis of TypeDec"
          ,Right (["f"], DepsT ["a", "b", "c"])]

    ]