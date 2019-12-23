module Data.Equal where

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

data EqualF h p = EqualF (h Int) (h Int) (p ~ Boolean)

instance hfunctorEqualF :: HFunctor EqualF where
  hmap g (EqualF x y p) = EqualF (g x) (g y) p

-- algebras

instance evalEqualF :: Eval EqualF a where
  eval (EqualF (Identity x) (Identity y) p) = Identity $ coerceSymm p $ x == y

instance evalValueEqualF :: EvalValue EqualF a where
  pEvalValue (EqualF (VInt x _) (VInt y _) p) = VBool (x == y) p

-- typelevel label

_equal = SProxy :: _ "equal"

-- row

type Equal r = (equal ∷ HProxy EqualF | r)

-- smart constructor

equal :: forall r. HEADT (Equal + r) Int -> HEADT (Equal + r) Int -> HEADT (Equal + r) Boolean
equal x y = review _EqualF (Tuple x (Tuple y identity))

-- classy prism

class AsEqualF s h p | s -> h p where
  _EqualF ∷ Prism' s (Tuple (h Int) (Tuple (h Int) (p ~ Boolean)))

instance asEqualFEqualF ∷ AsEqualF (EqualF h p) h p where
  _EqualF = prism' (\(Tuple x (Tuple y p)) -> EqualF x y p) (\(EqualF x y p) -> Just (Tuple x (Tuple y p)))

else instance asEqualFVariant :: (HFunctor h, AsEqualF (h f p) f p, TypeEquals (HVariantF (equal :: HProxy h | tail) f p) (HVariantF row f p)) => AsEqualF (HVariantF row f p) f p where
  _EqualF = dimap TE.from TE.to <<< _HVariantF _equal <<< _EqualF

else instance asEqualFMu :: (HFunctor h, AsEqualF (h (HMu h) p) f p) => AsEqualF (HMu h p) f p where
  _EqualF = re _HMu <<< _EqualF