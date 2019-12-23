module Data.Not where

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
import Prelude as P
import Type.Equality (class TypeEquals)
import Type.Equality as TE
import Type.Row (type (+))

-- base hfunctor

data NotF h p = NotF (h Boolean) (p ~ Boolean)

instance hfunctorNotF :: HFunctor NotF where
  hmap g (NotF x p) = NotF (g x) p

-- algebras

instance evalNotF :: Eval NotF where
  eval (NotF (Identity x) p) = Identity $ coerceSymm p $ P.not x

instance evalValueNotF :: EvalValue NotF where
  pEvalValue (NotF (VBool x _) p) = VBool (P.not x) p

-- typelevel label

_not = SProxy :: _ "not"

-- row

type Not r = (not ∷ HProxy NotF | r)

-- smart constructor

not :: forall r. HEADT (Not + r) Boolean -> HEADT (Not + r) Boolean
not x = review _NotF (Tuple x identity)

-- classy prism

class AsNotF s (h :: Type -> Type) p | s -> h p where
  _NotF ∷ Prism' s (Tuple (h Boolean) (p ~ Boolean))

instance asNotFNotF ∷ AsNotF (NotF h p) h p where
  _NotF = prism' (\(Tuple x p) -> NotF x p) (\(NotF x p) -> Just (Tuple x p))

else instance asNotFHVariantF :: (HFunctor h, AsNotF (h f p) f p, TypeEquals (HVariantF (not :: HProxy h | tail) f p) (HVariantF row f p)) => AsNotF (HVariantF row f p) f p where
  _NotF = dimap TE.from TE.to <<< _HVariantF _not <<< _NotF

else instance asNotFMu :: (HFunctor h, AsNotF (h (HMu h) p) f p) => AsNotF (HMu h p) f p where
  _NotF = re _HMu <<< _NotF