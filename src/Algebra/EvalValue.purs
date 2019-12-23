module Algebra.EvalValue where

import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Value (Value)
import HFunctor.Variant (HProxy, HVariantF)
import HFunctor.Variant as HVF
import Partial.Unsafe (unsafePartial)
import Prim.Row as R
import Prim.RowList as RL
import Type.Data.RowList (RLProxy(..))

class EvalValue h a where
  -- this is partial variant of algebra
  pEvalValue :: Partial => h Value a -> Value a

evalValue :: forall h a. EvalValue h a => h Value a -> Value a
evalValue = unsafePartial pEvalValue

class EvalValueHVFRL (rl :: RL.RowList) (row :: # Type) a | rl -> row where
  evalValueHVFRL :: RLProxy rl -> HVariantF row Value a -> Value a

instance evalValueHVFRLNil :: EvalValueHVFRL RL.Nil () a where
  evalValueHVFRL _ = HVF.case_

instance evalValueHVFRLCons :: (IsSymbol l, EvalValue h a, EvalValueHVFRL rl r a, R.Cons l (HProxy h) r r') => EvalValueHVFRL (RL.Cons l (HProxy h) rl) r' a where
  evalValueHVFRL _ = HVF.on l evalValue (evalValueHVFRL (RLProxy :: RLProxy rl)) where
    l = SProxy :: _ l

instance evalValueHVariantF :: (RL.RowToList row rl, EvalValueHVFRL rl row a) => EvalValue (HVariantF row) a where
  pEvalValue = evalValueHVFRL (RLProxy :: RLProxy rl)