module FRP.B.Type
  ( T : Set
  ) where

open import Function using (id; const; _∘_)

-- Behaviours are values which vary over time
B : Set → Set
B A = T → A

_→ᵇ_ : Set → Set → Set
a →ᵇ b = B (a → b)

idᵇ : {A : Set} → A →ᵇ A
idᵇ = const id

_∘ᵇ_ : {A B C : Set} → (B →ᵇ C) → (A →ᵇ B) → (A →ᵇ C)
f ∘ᵇ g = λ t → f t ∘ g t
