{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | This module implements a translator from Feldspar expressions
-- @translateExpr@, that reinterprets the Feldspar imperative
-- representation as actions in the @C@ monad.
--
-- Note. This module is temporary and should be replaced by a proper
-- rewrite of the Feldspar Compiler backend.
--
module Feldspar.Compiler.FromImperative
  ( translateExpr
  , translateTypeRep
  , translateType
  , compileType
  , feldsparCIncludes
  )
  where

import Control.Monad.State
import qualified Data.Map as Map

import Language.C.Quote.C
import qualified Language.C.Syntax as C
import qualified Feldspar as F
import qualified Feldspar.Core.Constructs as F
import Text.PrettyPrint.Mainland
import Feldspar.Core.Constructs (SyntacticFeld)
import Feldspar.Core.Types (TypeRep,defaultSize)
import Feldspar.Core.Middleend.FromTyped (untypeType)
import Feldspar.Compiler (feldsparCIncludes, defaultOptions)
import Feldspar.Compiler.Imperative.FromCore (fromCoreExp)
import qualified Feldspar.Compiler.Imperative.FromCore as FromCore
import Feldspar.Compiler.Imperative.Frontend (isArray,isNativeArray)
import Feldspar.Compiler.Imperative.Representation
import Feldspar.Compiler.Backend.C.CodeGeneration (isInfixFun)
import Language.C.Monad
import Language.Embedded.Expression


type instance VarPred F.Data = F.Type

-- | Evaluate `Data` expressions
instance EvalExp F.Data
  where
    litExp  = F.value
    evalExp = F.eval
    {-# INLINE litExp #-}
    {-# INLINE evalExp #-}

-- | Compile `Data` expressions
instance CompExp F.Data
  where
    varExp   = F.mkVariable
    compExp  = translateExpr
    compType = translateType
    {-# INLINE varExp #-}
    {-# INLINE compExp #-}
    {-# INLINE compType #-}

-- | Translate a Feldspar expression
translateExpr :: MonadC m => SyntacticFeld a => a -> m C.Exp
translateExpr a = do
  s <- get
  let als = Map.mapKeys fromInteger $ _aliases s
      ((es,ds,p,exp,ep),s')
        = flip runState (fromInteger $ _unique s)
        $ fromCoreExp defaultOptions als a
  put $ s { _unique = toInteger s' }
  mapM_ compileDeclaration ds
  mapM_ compileEntity es
  compileProgram p
  compileExpression exp
  -- TODO ep is currently ignored

translateTypeRep :: MonadC m => TypeRep a -> m C.Type
translateTypeRep trep = compileType
                      $ FromCore.compileType defaultOptions
                      $ untypeType trep (defaultSize trep)
{-# INLINE translateTypeRep #-}

compileEntity :: MonadC m => Entity () -> m ()
compileEntity StructDef{..} = do
  ms <- mapM compileStructMember structMembers
  addGlobal [cedecl| struct $id:structName { $sdecls:ms }; |]
compileEntity TypeDef{..} = do
  ty <- compileType actualType
  addGlobal [cedecl| typedef $ty:ty $id:typeName; |]
compileEntity Proc{..} = inFunction procName $ do
  mapM_ compileParam inParams
  let Left outs = outParams
  mapM_ compileParam outs
  inBlock $ maybe (return ()) compileBlock procBody
compileEntity ValueDef{..} = do
  ty <- compileType $ varType valVar
  is <- compileConstant valValue
  addGlobal [cedecl| $ty:ty $id:(varName valVar) = { $is }; |]

compileStructMember :: MonadC m => StructMember () -> m C.FieldGroup
compileStructMember StructMember{..} = do
  ty <- compileType structMemberType
  return [csdecl| $ty:ty $id:structMemberName; |]

compileParam :: MonadC m => Variable () -> m ()
compileParam Variable{..} = do
  ty <- compileType varType
  addParam [cparam| $ty:ty $id:varName |]

compileBlock :: MonadC m => Block () -> m ()
compileBlock Block{..} = do
  mapM_ compileDeclaration locals
  compileProgram blockBody

compileDeclaration :: MonadC m => Declaration () -> m ()
compileDeclaration Declaration{..} = do
  ty <- compileType $ varType declVar
  case initVal of
       Nothing  -> if isArray (varType declVar)
                      then addLocal [cdecl| $ty:ty $id:(varName declVar) = NULL; |]
                      else addLocal [cdecl| $ty:ty $id:(varName declVar); |]
       Just ini -> do
         e <- compileExpression ini
         addLocal [cdecl| $ty:ty $id:(varName declVar) = $e; |]

compileProgram :: MonadC m => Program () -> m ()
compileProgram Empty = return ()
compileProgram Comment{..} = addStms [cstms| ; /* comment */ |]
compileProgram Assign{..} = do
  l <- compileExpression lhs
  r <- compileExpression rhs
  addStm [cstm| $l = $r; |]
compileProgram ProcedureCall{..} = do
  as <- mapM compileActualParameter procCallParams
  addStm [cstm| $id:(procCallName) ( $args:as ) ; |]
compileProgram Sequence{..} = mapM_ compileProgram sequenceProgs
compileProgram Switch{..}
  | FunctionCall (Function "==" _) [_, _] <- scrutinee
  , [ (Pat (ConstExpr (BoolConst True )), Block [] (Sequence [Sequence [Assign vt et]]))
    , (Pat (ConstExpr (BoolConst False)), Block [] (Sequence [Sequence [Assign vf ef]]))
    ] <- alts
  , vt == vf
  = do
    s <- compileExpression scrutinee
    t <- compileExpression et
    f <- compileExpression ef
    v <- compileExpression vt
    addStm [cstm| $v = $s ? $t : $f; |]
compileProgram Switch{..} = do
  se <- compileExpression scrutinee
  case alts of
       [ (Pat (ConstExpr (BoolConst True)), tb) , (Pat (ConstExpr (BoolConst False)), eb) ] -> do
         tb' <- inNewBlock_ $ compileBlock tb
         eb' <- inNewBlock_ $ compileBlock eb
         case (tb',eb') of
           ([],[]) -> return ()
           (_ ,[]) -> addStm [cstm| if (   $se) {$items:tb'} |]
           ([],_ ) -> addStm [cstm| if ( ! $se) {$items:eb'} |]
           (_ ,_ ) -> addStm [cstm| if (   $se) {$items:tb'} else {$items:eb'} |]
       _ -> do
         is <- inNewBlock_ $ mapM_ compileAlt alts
         addStm [cstm| switch ($se) { $items:is } |]
compileProgram SeqLoop{..} = do
  cond  <- compileExpression sLoopCond
  items <- inNewBlock_ $ compileBlock sLoopBlock >> compileBlock sLoopCondCalc
  compileBlock sLoopCondCalc
    -- TODO Code duplication. If `sLoopCondCalc` is large, it's better to use
    --      `while(1)` with a conditional break inside.
  addStm [cstm| while ($cond) { $items:items } |]
compileProgram ParLoop{..} = do
  let ix = varName pLoopCounter
  it <- compileType $ varType pLoopCounter
  ib <- compileExpression pLoopEnd
  is <- compileExpression pLoopStep
  items <- inNewBlock_ $ compileBlock pLoopBlock
  addStm [cstm| for($ty:it $id:ix = 0; $id:ix < $ib; $id:ix += $is) { $items:items } |]
compileProgram BlockProgram{..} = inBlock $ compileBlock blockProgram

compileAlt :: MonadC m => (Pattern (), Block ()) -> m ()
compileAlt (PatDefault,b) = do
  ss <- inNewBlock_ $ compileBlock b
  addStm [cstm| default: { $items:ss break; } |]
compileAlt (Pat p,b) = do
  e  <- compileExpression p
  ss <- inNewBlock_ $ compileBlock b
  addStm [cstm| case $e : { $items:ss break; } |]

showType :: C.Type -> String
showType = flip displayS "" . renderCompact . ppr

compileActualParameter :: MonadC m => ActualParameter () -> m C.Exp
compileActualParameter ValueParameter{..} = compileExpression valueParam
compileActualParameter TypeParameter{..} = do
  ty <- compileType typeParam
  return [cexp| $id:(showType ty) |]
compileActualParameter FunParameter{..} = return [cexp| $id:funParamName |]

compileExpression :: MonadC m => Expression () -> m C.Exp
compileExpression VarExpr{..} = return [cexp| $id:(varName varExpr) |]
compileExpression e@ArrayElem{..} = do
  a <- compileExpression array
  i <- compileExpression arrayIndex
  t <- compileType $ typeof e
  return $ if isNativeArray $ typeof array
              then [cexp| $a[$i] |]
              else [cexp| at($id:(showType t),$a,$i) |]
compileExpression StructField{..} = do
  s <- compileExpression struct
  return [cexp| $s.$id:(fieldName) |]
compileExpression ConstExpr{..} = compileConstant constExpr
compileExpression FunctionCall{..} = do
  as <- mapM compileExpression funCallParams
  case () of
       _ | isInfixFun (funName function)
         , [a,b] <- as
         -> mkBinOp a b (funName function)
         | otherwise
         -> return [cexp| $id:(funName function)($args:as) |]
compileExpression Cast{..} = do
  ty <- compileType castType
  e  <- compileExpression castExpr
  return [cexp| ($ty:ty)($e) |]
compileExpression AddrOf{..} = do
  e <- compileExpression addrExpr
  return [cexp| &($e) |]
compileExpression SizeOf{..} = do
  ty <- compileType sizeOf
  return [cexp| sizeof($ty:ty) |]
compileExpression Deref{..} = do
  e <- compileExpression ptrExpr
  return [cexp| *($e) |]

mkBinOp :: MonadC m => C.Exp -> C.Exp -> String -> m C.Exp
mkBinOp a b = go
  where
    go "+"  = return [cexp| $a + $b |]
    go "-"  = return [cexp| $a - $b |]
    go "*"  = return [cexp| $a * $b |]
    go "/"  = return [cexp| $a / $b |]
    go "%"  = return [cexp| $a % $b |]
    go "==" = return [cexp| $a == $b |]
    go "!=" = return [cexp| $a != $b |]
    go "<"  = return [cexp| $a < $b |]
    go ">"  = return [cexp| $a > $b |]
    go "<=" = return [cexp| $a <= $b |]
    go ">=" = return [cexp| $a >= $b |]
    go "&&" = return [cexp| $a && $b |]
    go "||" = return [cexp| $a || $b |]
    go "&"  = return [cexp| $a & $b |]
    go "|"  = return [cexp| $a | $b |]
    go "^"  = return [cexp| $a ^ $b |]
    go "<<" = return [cexp| $a << $b |]
    go ">>" = return [cexp| $a >> $b |]
    -- go op   = throw $ UnhandledOperator op -- TODO

compileConstant :: MonadC m => Constant () -> m C.Exp
compileConstant IntConst{..} = return [cexp| $const:intValue |]
compileConstant DoubleConst{..} = return [cexp| $const:doubleValue |]
compileConstant FloatConst{..} = return [cexp| $const:floatValue |]
compileConstant BoolConst{..}
    | boolValue = addSystemInclude "stdbool.h" >> return [cexp| true |]
    | otherwise = addSystemInclude "stdbool.h" >> return [cexp| false |]
compileConstant ComplexConst{..} = do
  c1 <- compileConstant realPartComplexValue
  c2 <- compileConstant imagPartComplexValue
  return [cexp| $c1 + $c2 * I |]
compileConstant ArrayConst{..} = do
  cs <- mapM compileConstant arrayValues
  return [cexp| $exp:(head cs) |]

compileType :: MonadC m => Type -> m C.Type
compileType = go
  where
    go VoidType = return [cty| void |]
    go (MachineVector 1 BoolType) = do
      addSystemInclude "stdbool.h"
      return [cty| typename bool |]
    go (MachineVector 1 BitType)                  = return [cty| typename bit  |]
    go (MachineVector 1 FloatType)                = return [cty| float |]
    go (MachineVector 1 DoubleType)               = return [cty| double |]
    go (MachineVector 1 (ComplexType (MachineVector 1 FloatType)))  = do
      addSystemInclude "complex.h"
      return [cty| _Complex float |]
    go (MachineVector 1 (ComplexType (MachineVector 1 DoubleType)))  = do
      addSystemInclude "complex.h"
      return [cty| _Complex double |]
    go (ArrayType _ _)          = do
      addSystemInclude "feldspar_array.h"
      return [cty| struct array * |]
    go (NativeArray (Just 1) t) = go t
    go (NativeArray Nothing  t) = go t
    go (NativeArray (Just _) t) = do
      ty <- go t
      return [cty| $ty:ty*|]
    go (StructType n _)         = return [cty| struct $id:(n) |]
    go (MachineVector 1 (Pointer t)) = do
      ty <- go t
      return [cty| $ty:ty * |]
    go (IVarType _)             = return [cty| struct ivar |]
    go (MachineVector 1 (NumType sig sz)) = do
      addSystemInclude "stdint.h"
      let base = case sig of
                    Signed   -> "int"
                    Unsigned -> "uint"
      let size = case sz of
                    S8 -> "8"
                    S16 -> "16"
                    S32 -> "32"
                    S40 -> "40"
                    S64 -> "64"
      return [cty| typename $id:(concat [base,size,"_t"]) |]

-- | Extract the type of the expression as a C Type
translateType :: forall m expr a. (MonadC m, F.Type a) => expr a -> m C.Type
translateType _ = translateTypeRep (F.typeRep :: F.TypeRep a)
{-# INLINE translateType #-}
