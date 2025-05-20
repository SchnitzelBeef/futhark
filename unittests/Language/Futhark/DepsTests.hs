module Language.Futhark.DepsTests (tests) where

import Language.Futhark.Deps
import Test.Tasty
import Test.Tasty.HUnit
import Language.Futhark.Syntax

tests :: TestTree
tests =
  testGroup
    "Dependencies, unit tests"
    [ testCase "Tuples in conditional" $
        depsTestExp (Var (QualName {qualQuals = [], qualLeaf = VName "f" 4660}) (Info {unInfo = Scalar (Prim (Signed Int32))}) noLoc)
          @?= Right (DepVal (Ids [VName "f" 4660]), [])
    ]
