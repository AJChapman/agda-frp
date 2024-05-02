module FRP
  ( T : Set -- TODO: T should be totally ordered
  ) where

open import Data.List using (List)
open import Data.Product using (_×_)

data T̂ : Set where
  -∞   : T̂
  time : T → T̂
  ∞    : T̂

Bₐ : {A : Set} → Set
Bₐ {A} = T → A

Eₐ : {A : Set} → Set
Eₐ {A} = List (T̂ × A)
