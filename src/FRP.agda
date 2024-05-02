module FRP
  ( T : Set -- TODO: T should be totally ordered
  ) where

open import Data.List using (List)
open import Data.Product using (_×_)

data T̂ : Set where
  -∞   : T̂
  time : T → T̂
  ∞    : T̂

-- Behaviours are values which vary over time
B : (A : Set) → Set
B A = T → A

-- Events occur at certain points in time
E : (A : Set) → Set
E A = List (T̂ × A)
