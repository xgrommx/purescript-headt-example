module Data.Mul where

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

data MulF h p = MulF (h Int) (h Int) (p ~ Int)

instance hfunctorMulF :: HFunctor MulF where
  hmap g (MulF x y p) = MulF (g x) (g y) p

-- algebras

instance evalMulF :: Eval MulF a where
  eval (MulF (Identity x) (Identity y) p) = Identity $ coerceSymm p $ x * y

instance evalValueMulF :: EvalValue MulF a where
  pEvalValue (MulF (VInt x _) (VInt y _) p) = VInt (x * y) p

-- typelevel label

_mul = SProxy :: _ "mul"

-- row

type Mul r = (mul ∷ HProxy MulF | r)

-- smart constructor

mul :: forall r. HEADT (Mul + r) Int -> HEADT (Mul + r) Int -> HEADT (Mul + r) Int
mul x y = review _MulF (Tuple x (Tuple y identity))

-- classy prism

class AsMulF s h p | s -> h p where
  _MulF ∷ Prism' s (Tuple (h Int) (Tuple (h Int) (p ~ Int)))

instance asMulFMulF ∷ AsMulF (MulF h p) h p where
  _MulF = prism' (\(Tuple x (Tuple y p)) -> MulF x y p) (\(MulF x y p) -> Just (Tuple x (Tuple y p)))

else instance asMulFHVariantF :: (HFunctor h, AsMulF (h f p) f p, TypeEquals (HVariantF (mul :: HProxy h | tail) f p) (HVariantF row f p)) => AsMulF (HVariantF row f p) f p where
  _MulF = dimap TE.from TE.to <<< _HVariantF _mul <<< _MulF

else instance asMulFMu :: (HFunctor h, AsMulF (h (HMu h) p) f p) => AsMulF (HMu h p) f p where
  _MulF = re _HMu <<< _MulF