open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.Behavior.Type
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import Function using (id; _∘_; const)

open import FRP.T time using (T)
open import FRP.B time using (𝔹)

-- This is our behavior implementation.
-- For now it's identical to the denotation, but this
-- will change as we develop a more efficient implementation.
Behavior : Set a → Set a
Behavior A = T → A

_→ᵇ_ : Set a → Set a → Set a
a →ᵇ b = Behavior (a → b)

idᵇ : {A : Set a} → A →ᵇ A
idᵇ = const id

_∘ᵇ_ : {A B C : Set a} → (B →ᵇ C) → (A →ᵇ B) → (A →ᵇ C)
f ∘ᵇ g = λ t → f t ∘ g t

-- This maps from the behavior implementation to its denotation.
at : {A : Set a} → Behavior A → 𝔹 A
at = id
