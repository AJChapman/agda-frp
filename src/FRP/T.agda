module FRP.T
  ( T : Set -- TODO: T should be totally ordered
  ) where

data T̂ : Set where
  -∞ : T̂
  t  : T → T̂
  ∞  : T̂

