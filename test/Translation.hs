{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | Test that the expression translation is faithful to the code generated
-- from Feldspar.Compiler
--
module Main where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Exception

import Data.Loc (startPos)
import Data.DeriveTH
import Data.Derive.Arbitrary
import Data.String (fromString)

import Test.Tasty.TH
import Test.Tasty.QuickCheck as QC
import Test.QuickCheck

import Feldspar (Range(..),Length(..))
import Feldspar.Compiler (defaultOptions)
import Feldspar.Compiler.Imperative.Representation as FC
import Feldspar.Compiler.Backend.C.CodeGeneration as FC
import Feldspar.Compiler.FromImperative as FS
import Language.C.Monad

import Text.PrettyPrint as TPP
import Text.PrettyPrint.Mainland as MPP
import Language.C.Parser (parse,parseType)

derive makeArbitrary ''FC.Size
derive makeArbitrary ''FC.Signedness

floatingTypes :: Gen FC.Type
floatingTypes = MachineVector 1 <$> elements [ FC.FloatType, FC.DoubleType ]

numericTypes :: Gen FC.Type
numericTypes = oneof [ floatingTypes
                     , MachineVector 1 <$> (NumType <$> arbitrary <*> suchThat arbitrary (/=S40))
                     ]

complexTypes :: Gen FC.Type
complexTypes = MachineVector 1 <$> (ComplexType <$> floatingTypes)

arrayTypes :: Gen FC.Type
arrayTypes = ArrayType <$> pure (Range 4 4) <*> arbitrary

nativeArrayTypes :: Gen FC.Type
nativeArrayTypes = NativeArray <$> arbitrary <*> arbitrary

structTypes :: Gen FC.Type
structTypes = StructType <$> name <*> listOf fields
  where
    name = ('s':) <$> vectorOf 2 (elements ['a'..'z'])
    fields = do
      n <- ('f':) <$> listOf (elements ['a'..'z'])
      t <- arbitrary
      return (n,t)

referenceTypes :: Gen FC.Type
referenceTypes = do
  t <- oneof [ numericTypes, arrayTypes, structTypes, referenceTypes ]
  elements [ MachineVector 1 $ Pointer t
           , IVarType t
           ]

instance Arbitrary FC.Type where
    arbitrary = oneof [ elements [ FC.VoidType, FC.MachineVector 1 FC.BoolType ]
                      , numericTypes
                      -- , complexTypes
                      , arrayTypes
                      -- , nativeArrayTypes
                      , structTypes
                      , referenceTypes
                      ]

prop_types :: FC.Type -> Property
prop_types t = ioProperty $ do
    let ts = "bool"
           : [ s++"int"++show i++"_t" | s <- ["","u"], i <- [8,16,32,64] ]
    let t1 = FC.cgen (PEnv defaultOptions 0) t
    (t2,_) <- runCGen (compileType t) (defaultCEnv Flags)
    case parse [] ts parseType (fromString $ TPP.render t1) (startPos "") of
         Left e -> error (unlines [TPP.render t1, show e])
         Right t1' -> return $ show (MPP.ppr t1') === show (MPP.ppr t2)

main = $(defaultMainGenerator)
