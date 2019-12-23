module Algebra.EvalValue where

import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Value (Value)
import HFunctor.Variant (HProxy, HVariantF)
import HFunctor.Variant as HVF
import Higher (HAlgebra)
import Partial.Unsafe (unsafePartial)
import Prim.Row as R
import Prim.RowList as RL
import Type.Data.RowList (RLProxy(..))

class EvalValue h where
  -- this is partial variant of algebra
  pEvalValue :: Partial => HAlgebra h Value

evalValue :: forall h. EvalValue h => HAlgebra h Value
evalValue = unsafePartial pEvalValue

class EvalValueHVFRL (rl :: RL.RowList) (row :: # Type) | rl -> row where
  evalValueHVFRL :: RLProxy rl -> HAlgebra (HVariantF row) Value

instance evalValueHVFRLNil :: EvalValueHVFRL RL.Nil () where
  evalValueHVFRL _ = HVF.case_

instance evalValueHVFRLCons :: (IsSymbol l, EvalValue h, EvalValueHVFRL rl r, R.Cons l (HProxy h) r r') => EvalValueHVFRL (RL.Cons l (HProxy h) rl) r' where
  evalValueHVFRL _ = HVF.on l evalValue (evalValueHVFRL (RLProxy :: RLProxy rl)) where
    l = SProxy :: _ l

instance evalValueHVariantF :: (RL.RowToList row rl, EvalValueHVFRL rl row) => EvalValue (HVariantF row) where
  pEvalValue = evalValueHVFRL (RLProxy :: RLProxy rl)