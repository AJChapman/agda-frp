module FRP.Behavior
  ( T : Set
  ) where

open import Function using (id; _∘_; const)

open import FRP.Behavior.Type (T)
open import FRP.Behavior.Laws (T)

open import FRP.B (T)

time : Behavior T
time = id
