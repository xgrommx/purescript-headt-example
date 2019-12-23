module Data.If where

import Prelude

import Algebra.Eval (class Eval)
import Data.Either (Either)
import Algebra.EvalValue (class EvalValue)
import Data.Identity (Identity(..))
import Data.Leibniz (type (~))
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

data IfF h p = IfF (h Boolean) (h p) (h p) (Either (p ~ Int) (p ~ Boolean))

instance hfunctorIfF :: HFunctor IfF where
  hmap g (IfF c x y p) = IfF (g c) (g x) (g y) p

-- algebras

instance evalIfF :: Eval IfF a where
  eval (IfF (Identity c) (Identity x) (Identity y) _) = Identity $ if c then x else y

instance evalValueIfF :: EvalValue IfF a where
  pEvalValue (IfF (VBool c _) x y p) = if c then x else y

-- typelevel label

_if = SProxy :: _ "if_"

-- row

type If r = (if_ :: HProxy IfF | r)

-- smart constructor

if_ :: forall r p. HEADT (If + r) Boolean -> HEADT (If + r) p -> HEADT (If + r) p -> Either (p ~ Int) (p ~ Boolean) -> HEADT (If + r) p
if_ c x y p = review _IfF (Tuple c (Tuple x (Tuple y p)))

-- classy prism

class AsIfF s h p | s -> h p where
  _IfF ∷ Prism' s (Tuple (h Boolean) (Tuple (h p) (Tuple (h p) (Either (p ~ Int) (p ~ Boolean)))))

instance asIfFIfF ∷ AsIfF (IfF h p) h p where
  _IfF = prism' (\(Tuple c (Tuple x (Tuple y p))) -> IfF c x y p) (\(IfF c x y p) -> Just (Tuple c (Tuple x (Tuple y p))))

else instance asIfFHVariantF :: (HFunctor h, AsIfF (h f p) f p, TypeEquals (HVariantF (if_ :: HProxy h | tail) f p) (HVariantF row f p)) => AsIfF (HVariantF row f p) f p where
  _IfF = dimap TE.from TE.to <<< _HVariantF _if <<< _IfF

else instance asIfFMu :: (HFunctor h, AsIfF (h (HMu h) p) f p) => AsIfF (HMu h p) f p where
  _IfF = re _HMu <<< _IfF