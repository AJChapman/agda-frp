open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Semantics.Behavior.Type
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import Function using (id; const; _∘_)

open import FRP.Time Time using (T)

-- Behaviours are values which vary over time, i.e. functions from time to value
Behavior : Set a → Set a
Behavior A = T → A

_→ᵇ_ : Set a → Set a → Set a
a →ᵇ b = Behavior (a → b)

idᵇ : {A : Set a} → A →ᵇ A
idᵇ = const id

_∘ᵇ_ : {A B C : Set a} → (B →ᵇ C) → (A →ᵇ B) → (A →ᵇ C)
f ∘ᵇ g = λ t → f t ∘ g t
