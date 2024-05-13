open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.B.Type
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import Function using (id; const; _∘_)

open import FRP.T time using (T)

-- Behaviours are values which vary over time
𝔹 : Set a → Set a
𝔹 A = T → A

_→ᵇ_ : Set a → Set a → Set a
a →ᵇ b = 𝔹 (a → b)

idᵇ : {A : Set a} → A →ᵇ A
idᵇ = const id

_∘ᵇ_ : {A B C : Set a} → (B →ᵇ C) → (A →ᵇ B) → (A →ᵇ C)
f ∘ᵇ g = λ t → f t ∘ g t
