module Data.Val where

import Prelude

import Algebra.Eval (class Eval)
import Data.EvalValue (class EvalValue)
import Data.Identity (Identity(..))
import Data.Leibniz (type (~), coerceSymm)
import Data.Lens (Prism', prism', re, review)
import Data.Maybe (Maybe(..))
import Data.Profunctor (dimap)
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..))
import Data.Value (Value(..))
import HEADT (HEADT, _HMu, _HVariantF)
import HFunctor.Variant (HProxy, HVariantF)
import Higher (class HFunctor, HMu)
import Type.Equality (class TypeEquals)
import Type.Equality as TE
import Type.Row (type (+))

-- base hfunctor

data ValF (h :: Type -> Type) p = ValF Int (p ~ Int)

instance hfunctorValF :: HFunctor ValF where
  hmap _ (ValF x p) = ValF x p

-- algebras

instance evalValF :: Eval ValF a where
  eval (ValF x p) = Identity $ coerceSymm p $ x

instance evalValueValF :: EvalValue ValF a where
  pEvalValue (ValF x p) = VInt x p

-- typelevel label

_val = SProxy :: _ "val"

-- row 

type Val r = (val ∷ HProxy ValF | r)

-- smart constructor

val :: forall r. Int -> HEADT (Val + r) Int
val x = review _ValF (Tuple x identity)

-- classy prism

class AsValF s (h :: Type -> Type) p | s -> h p where
  _ValF ∷ Prism' s (Tuple Int (p ~ Int))

instance asValFValF ∷ AsValF (ValF h p) h p where
  _ValF = prism' (\(Tuple x p) -> ValF x p) (\(ValF x p) -> Just (Tuple x p))

else instance asValFHVariantF :: (HFunctor h, AsValF (h f p) f p, TypeEquals (HVariantF (val :: HProxy h | tail) f p) (HVariantF row f p)) => AsValF (HVariantF row f p) f p where
  _ValF = dimap TE.from TE.to <<< _HVariantF _val <<< _ValF

else instance asValFMu :: (HFunctor h, AsValF (h (HMu h) p) f p) => AsValF (HMu h p) f p where
  _ValF = re _HMu <<< _ValF