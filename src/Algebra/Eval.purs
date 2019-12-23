module Algebra.Eval where

import Data.Identity (Identity)
import Data.Symbol (class IsSymbol, SProxy(..))
import HFunctor.Variant (HProxy, HVariantF)
import HFunctor.Variant as HVF
import Prim.Row as R
import Prim.RowList as RL
import Type.Data.RowList (RLProxy(..))

class Eval h a where
  eval :: h Identity a -> Identity a

class EvalHVFRL (rl :: RL.RowList) (row :: # Type) a | rl -> row where
  evalHVFRL :: RLProxy rl -> HVariantF row Identity a -> Identity a

instance evalHVFRLNil :: EvalHVFRL RL.Nil () a where
  evalHVFRL _ = HVF.case_

instance evalHVFRLCons :: (IsSymbol l, Eval h a, EvalHVFRL rl r a, R.Cons l (HProxy h) r r') => EvalHVFRL (RL.Cons l (HProxy h) rl) r' a where
  evalHVFRL _ = HVF.on l eval (evalHVFRL (RLProxy :: RLProxy rl)) where
    l = SProxy :: _ l

instance evalHVariantF :: (RL.RowToList row rl, EvalHVFRL rl row a) => Eval (HVariantF row) a where
  eval = evalHVFRL (RLProxy :: RLProxy rl)