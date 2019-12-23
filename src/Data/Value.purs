module Data.Value where

import Prelude

import Data.Leibniz (type (~), coerceSymm)

data Value a
  = VInt Int (a ~ Int)
  | VBool Boolean (a ~ Boolean)

instance showValue :: Show a => Show (Value a) where
  show = case _ of
    VInt a p -> "VInt " <> show (coerceSymm p a)
    VBool a p -> "VBool " <> show (coerceSymm p a)