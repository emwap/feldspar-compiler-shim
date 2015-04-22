{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

-- | Conversion from 'Program' to 'M'
module Feldspar.Compiler.ToMutable
  ( Store
  , GenM
  , local
  , ToMutable (..)
  , toMutable
  ) where



import Control.Monad.State.Strict
import Data.Dynamic
import Data.Map (Map)
import qualified Data.Map as Map

import Feldspar (Data, M)
import qualified Feldspar as Feld

import Control.Monads
import Language.Embedded.Imperative

import Feldspar.Compiler.FromImperative ()



-- | Store for state variables
type Store = Map String Dynamic

-- | Monad for generating 'M' programs
type GenM = StateT Store (SupplyT M)

-- | Run a 'GenM' in a local scope
local :: GenM a -> GenM (M a)
local m = do
    store <- get
    v     <- lift $ SupplyT get
    lift $ SupplyT $ put (v+100) -- TODO Use a splittable supply
    return $ flip evalStateT v $ unSupplyT $ flip evalStateT store m

-- | Instructions that can be converted to the 'M' monad
class ToMutable instr
  where
    -- | Convert an instruction to the 'M' monad
    toMutCMD :: instr GenM a -> a -> GenM a

instance (ToMutable i1, ToMutable i2) => ToMutable (i1 :+: i2)
  where
    toMutCMD (Inl i) = toMutCMD i
    toMutCMD (Inr i) = toMutCMD i

-- | Conversion from 'Program' to 'M'
toMutable :: (ToMutable instr, DryInterp instr, MapInstr instr) => Program instr a -> M a
toMutable = runSupplyT . flip evalStateT Map.empty . observe toMutCMD

deriving instance Typeable Feld.Ref -- TODO Should go into Feldspar

showVar :: VarId -> String
showVar = ('v':) . show

instance ToMutable (RefCMD Data)
  where
    toMutCMD cmd@NewRef r@(RefComp v) = do
        fr <- fNewRef cmd
        modify $ Map.insert (showVar v) $ toDyn fr
        return r
    toMutCMD cmd@(InitRef _) r@(RefComp v) = do
        fr <- fNewRef cmd
        modify $ Map.insert (showVar v) $ toDyn fr
        return r
    toMutCMD (GetRef (RefComp v)) _ = do
        Just fr <- fmap fromDynamic $ gets (Map.! showVar v)
        lift $ lift $ Feld.getRef fr
    toMutCMD (SetRef (RefComp v) a) _ = do
        Just fr <- fmap fromDynamic $ gets (Map.! showVar v)
        lift $ lift $ Feld.setRef fr a

-- | Helper function to resolve the overloading of 'Feld.newRef'
fNewRef :: RefCMD Data GenM (Ref a) -> GenM (Feld.Ref (Data a))
fNewRef NewRef      = lift $ lift $ Feld.newRef Feld.undef
fNewRef (InitRef a) = lift $ lift $ Feld.newRef a

instance ToMutable (ArrCMD Data)
  where
    toMutCMD (NewArr n a) arr@(ArrComp v) = do
        let Just n' = cast n  -- TODO
        fa <- lift $ lift $ Feld.newArr n' a
        modify $ Map.insert v $ toDyn fa
        return arr
--     toMutCMD (GetArr i (ArrComp v)) _ = do
--         let Just i' = cast i  -- TODO
--         Just fa <- fmap fromDynamic $ gets (Map.! v)
--         a <- lift $ lift $ Feld.getArr fa i'
--         return ()
--     toMutCMD (SetArr i a (ArrComp v)) _ = do
--         let Just i' = cast i  -- TODO
--         Just fa <- fmap fromDynamic $ gets (Map.! v)
--         lift $ lift $ Feld.setArr fa i' a

instance ToMutable (ControlCMD Data)
  where
    toMutCMD (If c tm fm) _ = do
        t <- local tm
        f <- local fm
        lift $ lift $ Feld.ifM c t f
    toMutCMD (While contm bodym) _ = do
        cont <- local contm
        body <- local bodym
        lift $ lift $ Feld.whileM cont body



-- Testing

prog :: Program (RefCMD Data :+: ControlCMD Data) (Data Feld.Int32)
prog = do
    ir <- initRef (0 :: Data Feld.Int32)
    ar <- initRef (1 :: Data Feld.Int32)
    xr <- initRef (6 :: Data Feld.Int32)
    setRef xr 67
    x1 <- getRef xr
    while
        (do i <- getRef ir; setRef ir (i+1); return (i Feld.< 10))
        (do a <- getRef ar; setRef ar (a*2))
    setRef xr 102
    x2 <- getRef xr
    a  <- getRef ar
    return (x1+x2+a)

test1 = Feld.drawAST $ toMutable prog
test2 = Feld.eval $ toMutable prog

