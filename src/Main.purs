module Main where

import Prelude hiding (add,not,mul)

import Algebra.Eval (eval)
import Data.Add (Add, add)
import Data.Bool (Bool, bool)
import Data.Either (Either(..))
import Data.Equal (Equal, equal)
import Data.EvalValue (evalValue)
import Data.If (If, if_)
import Data.Mul (Mul, mul)
import Data.Not (Not, not)
import Data.Val (Val, val)
import Effect (Effect)
import Effect.Class.Console (logShow)
import HEADT (HEADT)
import Higher (hcata)
import Type.Row (type (+))

expr :: HEADT (Val + Add + ()) Int
expr = add (val 12) (val 30)

expr2 :: HEADT (Val + Add + Equal + ()) Boolean
expr2 = equal (val 10) (val 20)

expr3 :: HEADT (Val + Add + Equal + Not + ()) Boolean
expr3 = not (equal (val 10) (val 20))

expr4 :: HEADT (Not + Equal + Mul + Add + Val + ()) Boolean
expr4 = not (equal (mul (val 10) (val 1)) (add (val 0) (val 1)))

expr5 :: HEADT (If + Bool + Add + Val + ()) Int
expr5 = if_ (bool false) (val 16) (add (val 42) (val 45)) (Left identity)

main :: Effect Unit
main = do
  logShow $ hcata eval expr
  logShow $ hcata eval expr2
  logShow $ hcata eval expr3
  logShow $ hcata eval expr4
  logShow $ hcata eval expr5
  logShow $ hcata evalValue expr
  logShow $ hcata evalValue expr2
  logShow $ hcata evalValue expr3
  logShow $ hcata evalValue expr4
  logShow $ hcata evalValue expr5