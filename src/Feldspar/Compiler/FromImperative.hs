{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
  )
  where

import Control.Monad.State

import Language.C.Quote.C
import qualified Language.C.Syntax as C
import qualified Feldspar as F
import Text.PrettyPrint.Mainland (ppr)
import Feldspar.Core.Constructs (SyntacticFeld)
import Feldspar.Core.Types (TypeRep,defaultSize)
import Feldspar.Core.Middleend.FromTyped (untypeType)
import Feldspar.Compiler (defaultOptions)
import Feldspar.Compiler.Imperative.FromCore (fromCoreM)
import Feldspar.Compiler.Imperative.Frontend (isVarExpr,isNativeArray,isArray)
import Feldspar.Compiler.Imperative.Representation
import Feldspar.Compiler.Imperative.FromCore.Interpretation (compileTypeRep)
import Feldspar.Compiler.Backend.C.MachineLowering (rename)
import Feldspar.Compiler.Backend.C.CodeGeneration (isInfixFun)
import Language.C.Monad

-- | Translate a Feldspar expression
translateExpr :: MonadC m => SyntacticFeld a => a -> m C.Exp
translateExpr a = do
  s <- get
  let (ast,s') = flip runState (_unique s)
               $ fromCoreM defaultOptions "test" a
  put $ s { _unique = s' }
  translateExpr' $ rename defaultOptions False ast

translateTypeRep :: MonadC m => TypeRep a -> m C.Type
translateTypeRep trep = compileType $ compileTypeRep defaultOptions $ untypeType trep (defaultSize trep)
{-# INLINE translateTypeRep #-}

-- | Reinterpet the Feldspar imperative representation as actions in the
-- @C@ monad.
--
translateExpr' :: MonadC m => Module () -> m C.Exp
translateExpr' Module{..}
  | (x:xs) <- reverse entities
  , Proc{..} <- x
  , "test" == procName
  , Just (Block ds body) <- procBody
  , Left [out] <- outParams
  , Sequence [Sequence{..}] <- body
  , (p:ps) <- reverse sequenceProgs
  = do
    mapM_ compileDeclaration ds
    mapM_ compileEntity $ reverse xs
    mapM_ compileProgram $ reverse ps
    translatePrg out p
translateExpr' a = error $ unlines ["Can't translate expression from module:", show a]

deref :: Type -> Type
deref (MachineVector 1 (Pointer t)) = deref t
deref t           = t

translatePrg :: MonadC m => Variable () -> Program () -> m C.Exp
translatePrg _ ProcedureCall{..}
  | "copy" == procCallName
  , [_,rhs] <- procCallParams
  = compileActualParameter rhs
translatePrg v (Assign (Just (Deref e)) rhs)
  | isVarExpr e
  , varName v == varName (varExpr e)
  = compileExpression rhs
translatePrg Variable{..} Sequence{..}
  | [Assign _ _,ProcedureCall{..}] <- sequenceProgs
  , "copyArray" <- procCallName
  , [_,rhs] <- procCallParams
  = compileActualParameter rhs
  | [Assign _ rhs] <- sequenceProgs
  = compileExpression rhs
translatePrg Variable{..} Switch{..}
  | FunctionCall (Function "==" _) [_, _] <- scrutinee
  , [ (Pat (ConstExpr (BoolConst True )), Block [] (Sequence [Sequence [Assign (Just vt) et]]))
    , (Pat (ConstExpr (BoolConst False)), Block [] (Sequence [Sequence [Assign (Just vf) ef]]))
    ] <- alts
  , vt == vf
  = do
    s <- compileExpression scrutinee
    t <- compileExpression et
    f <- compileExpression ef
    return [cexp| $s ? $t : $f |]
translatePrg Variable{..} a = do
  var <- gensym "v"
  ty  <- compileType $ deref varType
  addLocal [cdecl| $ty:ty $id:var = 0; |]
  inBlock $ do
    addLocal [cdecl| $ty:ty * $id:varName = & $id:var; |]
    compileProgram a
    when (isArray $ deref varType) $ addStm [cstm| $id:var = *$id:varName; |]
  return [cexp| $id:var |]

compileModule :: MonadC m => Module () -> m ()
compileModule Module{..} = mapM_ compileEntity entities

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
       Nothing  -> addLocal [cdecl| $ty:ty $id:(varName declVar); |]
       Just ini -> do
         e <- compileExpression ini
         addLocal [cdecl| $ty:ty $id:(varName declVar) = $e; |]

compileProgram :: MonadC m => Program () -> m ()
compileProgram Empty = return ()
compileProgram Comment{..} = addStms [cstms| ; /* comment */ |]
compileProgram Assign{..}
  | Just e <- lhs
  = do
      l <- compileExpression e
      r <- compileExpression rhs
      addStm [cstm| $l = $r; |]
compileProgram Assign{} = return ()
compileProgram ProcedureCall{..} = do
  as <- mapM compileActualParameter procCallParams
  addStm [cstm| $id:(procCallName) ( $args:as ) ; |]
compileProgram Sequence{..} = mapM_ compileProgram sequenceProgs
compileProgram Switch{..}
  | FunctionCall (Function "==" _) [_, _] <- scrutinee
  , [ (Pat (ConstExpr (BoolConst True )), Block [] (Sequence [Sequence [Assign (Just vt) et]]))
    , (Pat (ConstExpr (BoolConst False)), Block [] (Sequence [Sequence [Assign (Just vf) ef]]))
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
         addStm [cstm| if ($se) { $items:tb' } else { $items:eb' } |]
       _ -> do
         is <- inNewBlock_ $ mapM_ compileAlt alts
         addStm [cstm| switch ($se) { $items:is } |]
compileProgram SeqLoop{..} = do
  cond  <- compileExpression sLoopCond
  items <- inNewBlock_ $ compileBlock sLoopBlock >> compileBlock sLoopCondCalc
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

compileActualParameter :: MonadC m => ActualParameter () -> m C.Exp
compileActualParameter ValueParameter{..} = compileExpression valueParam
compileActualParameter TypeParameter{..} = do
  ty <- compileType typeParam
  return [cexp| $id:(show $ ppr ty) |]
compileActualParameter FunParameter{..} = return [cexp| $id:funParamName |]

compileExpression :: MonadC m => Expression () -> m C.Exp
compileExpression VarExpr{..} = return [cexp| $id:(varName $ varExpr) |]
compileExpression e@ArrayElem{..} = do
  a <- compileExpression array
  i <- compileExpression arrayIndex
  t <- compileType $ typeof e
  return $ if isNativeArray $ typeof array
              then [cexp| $a[$i] |]
              else [cexp| at($id:(show $ ppr t),$a,$i) |]
compileExpression StructField{..} = do
  s <- compileExpression struct
  return [cexp| $s.$id:(fieldName) |]
compileExpression ConstExpr{..} = compileConstant constExpr
compileExpression FunctionCall{..} = do
  as <- mapM compileExpression funCallParams
  case () of
       _ | funName function == "!"
         -> return [cexp| at($args:as) |]
         | isInfixFun (funName function)
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
compileConstant BoolConst{..} = return [cexp| $const:(if boolValue then 0 else 1 :: Int) |]
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
    go VoidType                 = return [cty| void |]
    go (MachineVector 1 BoolType)                 = return [cty| typename bool |]
    go (MachineVector 1 BitType)                  = return [cty| typename bit  |]
    go (MachineVector 1 FloatType)                = return [cty| float |]
    go (MachineVector 1 DoubleType)               = return [cty| double |]
    go (MachineVector 1 (ComplexType (MachineVector 1 FloatType)))  = do
      addSystemInclude "complex.h"
      addTypedef [cedecl| $esc:("#define floatcmplx float complex") |]
      return [cty| typename floatcmplx |]
    go (MachineVector 1 (ComplexType (MachineVector 1 DoubleType)))  = do
      addSystemInclude "complex.h"
      addTypedef [cedecl| $esc:("#define doublecmplx double complex") |]
      return [cty| typename doublecmplx |]
    go (MachineVector 1 (ComplexType t)) = do
      addSystemInclude "complex.h"
      ty <- go t
      return [cty| $ty:ty complex |]
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
      return [cty| typename $id:(base++size++"_t") |]

-- | Extract the type of the expression as a C Type
translateType :: forall m expr a. (MonadC m, F.Type a) => expr a -> m C.Type
translateType _ = translateTypeRep (F.typeRep :: F.TypeRep a)
{-# INLINE translateType #-}
