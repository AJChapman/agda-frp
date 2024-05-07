module FRP.Behavior
  ( T : Set
  ) where

open import Function using (id; _∘_)

open import FRP.B (T)

-- This is our behavior implementation.
-- For now it's identical to the denotation, but this
-- will change as we develop a more efficient implementation.
Behavior : Set → Set
Behavior A = T → A

-- This maps from the behavior implementation to its denotation.
at : {A : Set} → Behavior A → B A
at = id

fmap : {A B : Set} → (A → B) → Behavior A → Behavior B
fmap f b = f ∘ b
