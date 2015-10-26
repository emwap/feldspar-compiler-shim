import qualified Prelude

import Feldspar
import Language.Embedded.Imperative

import Feldspar.Compiler.ToMutable




prog :: Program (RefCMD Data :+: ControlCMD Data) (Data Int32)
prog = do
    ir <- initRef (0 :: Data Int32)
    ar <- initRef (1 :: Data Int32)
    xr <- initRef (6 :: Data Int32)
    setRef xr 67
    x1 <- getRef xr
    while
        (do i <- getRef ir; setRef ir (i+1); return (i < 10))
        (do a <- getRef ar; setRef ar (a*2))
    setRef xr 102
    x2 <- getRef xr
    a  <- getRef ar
    return (x1+x2+a)

main = do
    drawAST $ toMutable prog
    x <- eval $ toMutable prog
    if x Prelude.== 1193
      then return ()
      else fail ("wrong result " Prelude.++ show x)

