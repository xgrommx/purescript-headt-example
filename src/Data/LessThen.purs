module Data.LessThen where

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

data LessThanF h p = LessThanF (h Int) (h Int) (p ~ Boolean)

instance hfunctorLessThanF :: HFunctor LessThanF where
  hmap g (LessThanF x y p) = LessThanF (g x) (g y) p

-- algebras

instance evalLessThanF :: Eval LessThanF a where
  eval (LessThanF (Identity x) (Identity y) p) = Identity $ coerceSymm p $ x < y

instance evalValueLessThanF :: EvalValue LessThanF a where
  pEvalValue (LessThanF (VInt x _) (VInt y _) p) = VBool (x < y) p

-- typelevel label

_lessThan = SProxy :: _ "lessThan"

-- row

type LessThan r = (lessThan :: HProxy LessThanF | r)

-- smart constructor

lessThan :: forall r. HEADT (LessThan + r) Int -> HEADT (LessThan + r) Int -> HEADT (LessThan + r) Boolean
lessThan x y = review _LessThanF (Tuple x (Tuple y identity))

-- classy prism

class AsLessThanF s h p | s -> h p where
  _LessThanF ∷ Prism' s (Tuple (h Int) (Tuple (h Int) (p ~ Boolean)))

instance asLessThanFLessThanF ∷ AsLessThanF (LessThanF h p) h p where
  _LessThanF = prism' (\(Tuple x (Tuple y p)) -> LessThanF x y p) (\(LessThanF x y p) -> Just (Tuple x (Tuple y p)))

else instance asLessThanFHVariantF :: (HFunctor h, AsLessThanF (h f p) f p, TypeEquals (HVariantF (lessThan :: HProxy h | tail) f p) (HVariantF row f p)) => AsLessThanF (HVariantF row f p) f p where
  _LessThanF = dimap TE.from TE.to <<< _HVariantF _lessThan <<< _LessThanF

else instance asLessThanFMu :: (HFunctor h, AsLessThanF (h (HMu h) p) f p) => AsLessThanF (HMu h p) f p where
  _LessThanF = re _HMu <<< _LessThanF