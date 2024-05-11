module FRP.Behavior.Type
  ( T : Set
  ) where

open import Function using (id; _∘_; const)

open import FRP.B (T) using (𝔹)

-- This is our behavior implementation.
-- For now it's identical to the denotation, but this
-- will change as we develop a more efficient implementation.
Behavior : Set → Set
Behavior A = T → A

_→ᵇ_ : Set → Set → Set
a →ᵇ b = Behavior (a → b)

idᵇ : {A : Set} → A →ᵇ A
idᵇ = const id

_∘ᵇ_ : {A B C : Set} → (B →ᵇ C) → (A →ᵇ B) → (A →ᵇ C)
f ∘ᵇ g = λ t → f t ∘ g t

-- This maps from the behavior implementation to its denotation.
at : {A : Set} → Behavior A → 𝔹 A
at = id
