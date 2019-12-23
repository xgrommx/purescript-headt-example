module Data.Add where

import Prelude

import Algebra.Eval (class Eval)
import Algebra.EvalValue (class EvalValue)
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

data AddF h p = AddF (h Int) (h Int) (p ~ Int)

instance hfunctorAddF :: HFunctor AddF where
  hmap g (AddF x y p) = AddF (g x) (g y) p

-- algebras

instance evalAddF :: Eval AddF a where
  eval (AddF (Identity x) (Identity y) p) = Identity $ coerceSymm p $ x + y

instance evalValueAddF :: EvalValue AddF a where
  pEvalValue (AddF (VInt x _) (VInt y _) p) = VInt (x + y) p

-- typelevel label

_add = SProxy :: _ "add"

-- row

type Add r = (add ∷ HProxy AddF | r)

-- smart constructor

add :: forall r. HEADT (Add + r) Int -> HEADT (Add + r) Int -> HEADT (Add + r) Int
add x y = review _AddF (Tuple x (Tuple y identity))

-- classy prism

class AsAddF s h p | s -> h p where
  _AddF ∷ Prism' s (Tuple (h Int) (Tuple (h Int) (p ~ Int)))

instance asAddFAddF ∷ AsAddF (AddF h p) h p where
  _AddF = prism' (\(Tuple x (Tuple y p)) -> AddF x y p) (\(AddF x y p) -> Just (Tuple x (Tuple y p)))

else instance asAddFHVariantF :: (HFunctor h, AsAddF (h f p) f p, TypeEquals (HVariantF (add :: HProxy h | tail) f p) (HVariantF row f p)) => AsAddF (HVariantF row f p) f p where
  _AddF = dimap TE.from TE.to <<< _HVariantF _add <<< _AddF

else instance asAddFMu :: (HFunctor h, AsAddF (h (HMu h) p) f p) => AsAddF (HMu h p) f p where
  _AddF = re _HMu <<< _AddF