module Algebra.Eval where

import Data.Identity (Identity)
import Data.Symbol (class IsSymbol, SProxy(..))
import HFunctor.Variant (HProxy, HVariantF)
import HFunctor.Variant as HVF
import Higher (HAlgebra)
import Prim.Row as R
import Prim.RowList as RL
import Type.Data.RowList (RLProxy(..))

class Eval h where
  eval :: HAlgebra h Identity

class EvalHVFRL (rl :: RL.RowList) (row :: # Type) | rl -> row where
  evalHVFRL :: RLProxy rl -> HAlgebra (HVariantF row) Identity

instance evalHVFRLNil :: EvalHVFRL RL.Nil () where
  evalHVFRL _ = HVF.case_

instance evalHVFRLCons :: (IsSymbol l, Eval h, EvalHVFRL rl r, R.Cons l (HProxy h) r r') => EvalHVFRL (RL.Cons l (HProxy h) rl) r' where
  evalHVFRL _ = HVF.on l eval (evalHVFRL (RLProxy :: RLProxy rl)) where
    l = SProxy :: _ l

instance evalHVariantF :: (RL.RowToList row rl, EvalHVFRL rl row) => Eval (HVariantF row) where
  eval = evalHVFRL (RLProxy :: RLProxy rl)