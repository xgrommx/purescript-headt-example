module Data.Bool where

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

data BoolF (h :: Type -> Type) p = BoolF Boolean (p ~ Boolean)

instance hfunctorBoolF :: HFunctor BoolF where
  hmap _ (BoolF x p) = BoolF x p

-- algebras

instance evalBoolF :: Eval BoolF a where
  eval (BoolF x p) = Identity $ coerceSymm p $ x

instance evalValueBoolF :: EvalValue BoolF a where
  pEvalValue (BoolF x p) = VBool x p

-- typelevel label

_bool = SProxy :: _ "bool"

-- row

type Bool r = (bool :: HProxy BoolF | r)

-- smart constructor

bool :: forall r. Boolean -> HEADT (Bool + r) Boolean
bool x = review _BoolF (Tuple x identity)

-- classy prism

class AsBoolF s (h :: Type -> Type) p | s -> h p where
  _BoolF ∷ Prism' s (Tuple Boolean (p ~ Boolean))

instance asBoolFBoolF ∷ AsBoolF (BoolF h p) h p where
  _BoolF = prism' (\(Tuple x p) -> BoolF x p) (\(BoolF x p) -> Just (Tuple x p))

else instance asBoolFHVariantF :: (HFunctor h, AsBoolF (h f p) f p, TypeEquals (HVariantF (bool :: HProxy h | tail) f p) (HVariantF row f p)) => AsBoolF (HVariantF row f p) f p where
  _BoolF = dimap TE.from TE.to <<< _HVariantF _bool <<< _BoolF

else instance asBoolFMu :: (HFunctor h, AsBoolF (h (HMu h) p) f p) => AsBoolF (HMu h p) f p where
  _BoolF = re _HMu <<< _BoolF