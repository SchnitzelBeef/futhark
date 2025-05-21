module Language.Futhark.DepsTests (tests) where

import Language.Futhark.Deps
import Test.Tasty
import Test.Tasty.HUnit
import Language.Futhark.Syntax
import Data.Char (ord) 

-- | Generates a very simple Var expression for testing 
generateVar :: Char -> ExpBase Info VName
generateVar name =
  Var 
    (QualName {qualQuals = [], qualLeaf = VName (nameFromString [name]) (ord name)})
    (Info {unInfo = Scalar (Prim (Signed Int32))})
    noLoc

-- | Shorthand for creating a literal that isn't bound to a variable
getLit :: ExpBase Info VName 
getLit = Literal (SignedValue $ Int8Value 0) noLoc

-- | Extracts the variable name from a simple variable expression
getVName :: ExpBase Info VName -> VName
getVName (Var qn _ _) = qualLeaf qn
getVName _ = VName (nameFromString "Error") 0

-- | Shorthand for some bogus Info that is not applied in the interpreter
getStructType :: TypeBase dim u
getStructType = Scalar (Prim Bool)

-- | Shorthand for some bogus Info that is not applied in the interpreter
getInfo :: Info (TypeBase dim u)
getInfo = Info {unInfo = Scalar (Prim (Signed Int32))}

-- | Shorthand for some bogus Info that is not applied in the interpreter
getAppResInfo :: Info AppRes 
getAppResInfo = (Info {unInfo = AppRes {appResType = getStructType, appResExt = []}})

-- | Shorthand for some bogus Info that is not applied in the interpreter
getIdentBase :: ExpBase Info VName -> IdentBase Info VName (TypeBase dim6 u2)
getIdentBase e = Ident {identName = getVName e, identType = Info {unInfo = Scalar (Prim (Signed Int32))}, identSrcLoc = noLoc}

tests :: TestTree
tests =
  testGroup
    "Dependencies"
    [ 
      {- 
          if c
            then (x, z)
            else (y, z)
      -}
      testCase "Injection into tuples" $
        let c = generateVar 'c'
            x = generateVar 'x'
            y = generateVar 'y'
            z = generateVar 'z'
        in 
          depsTestExp
            (AppExp 
              (If c
                (TupLit [x, z] noLoc)
                (TupLit [y, getLit] noLoc) noLoc)
              getAppResInfo)
          @?= Right ( 
            DepTuple [ -- Outer deps
              DepVal (Ids [getVName c, getVName x, getVName y]),
              DepVal (Ids [getVName c, getVName z])],
            []), -- Inner deps, none because there is no let-binding

      {- Fixed point test corresponding to the code:  
          let x = 
            loop p = (a, b, c) for i < n do
              (p.1, p.2, p.0)
          in x.0
        -}
      testCase "Fixed point iteration in loop" $
        let x = generateVar 'x'
            p = generateVar 'p'
            a = generateVar 'a'
            b = generateVar 'b'
            c = generateVar 'c'
            i = generateVar 'i'
            n = generateVar 'n'
        in
          depsTestExp
            (AppExp 
              (LetPat
                []
                (Id (getVName x) getInfo noLoc)
                (AppExp 
                  (Loop []
                    (Id (getVName p) getInfo noLoc) 
                    (LoopInitExplicit (TupLit [a, b, c] noLoc))
                    (For (getIdentBase i) n)
                    (TupLit [ -- Cycles tuple
                        Project (nameFromString "1") p getInfo noLoc, 
                        Project (nameFromString "2") p getInfo noLoc,
                        Project (nameFromString "0") p getInfo noLoc
                        ] noLoc)
                    noLoc)
                  getAppResInfo)
                (Project (nameFromString "0") x getInfo noLoc)
                noLoc
              )
              getAppResInfo)
            @?= Right (
                -- Outer deps, the getInfotion depends on all variables except i, p, and x
                DepVal (Ids [getVName a, getVName b, getVName c, getVName n]),
                -- Inner deps, x depends on all variables except i, p, and x for all three values in it's tuple
                -- (because of the variables were cycled in the loop)
                [ Depends (Name $ getVName x) 
                  (DepTuple[ DepVal (Ids [getVName a, getVName b, getVName c, getVName n]),
                            DepVal (Ids [getVName a, getVName b, getVName c, getVName n]),
                            DepVal (Ids [getVName a, getVName b, getVName c, getVName n])])])
    ]

