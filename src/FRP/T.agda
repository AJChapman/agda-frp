open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.T
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Decidable using (yes; no)

open DecTotalOrder time renaming
  ( Carrier to T
  ; _≈_ to _≈ₜ_
  ; _≤_ to _≤ₜ_
  ; _≤?_ to _≤ₜ?_
  ; _≟_ to _≟ₜ_
  ) public

data T̂ : Set a where
  -∞ : T̂
  t  : T → T̂
  ∞  : T̂

infix 4 _≈ᵗ_ _≤ᵗ_ _≤ᵗ_ _≟ᵗ_

data _≈ᵗ_ : T̂ → T̂ → Set (a ⊔ suc ℓ) where
  -∞-refl : -∞ ≈ᵗ -∞
  ∞-refl :   ∞ ≈ᵗ  ∞
  t-refl : ∀{t₁ t₂ : T} → t₁ ≈ₜ t₂ → t t₁ ≈ᵗ t t₂

data _≤ᵗ_ : T̂ → T̂ → Set (a ⊔ suc ℓ) where
  -∞-≤ᵗ : ∀{t₂ : T̂} → -∞ ≤ᵗ t₂
  ≤ᵗ-∞  : ∀{t₁ : T̂} → t₁ ≤ᵗ ∞
  t-≤ᵗ  : ∀{t₁ t₂ : T} → t₁ ≤ₜ t₂ → t t₁ ≤ᵗ t t₂

_≤ᵗ?_ : Decidable _≤ᵗ_
-∞   ≤ᵗ?  _   = yes -∞-≤ᵗ
_    ≤ᵗ?  ∞   = yes  ≤ᵗ-∞
∞    ≤ᵗ? -∞   = no λ ()
t t₁ ≤ᵗ? -∞   = no λ ()
∞    ≤ᵗ? t t₂ = no λ ()
t t₁ ≤ᵗ? t t₂ with t₁ ≤ₜ? t₂
...             | (yes p) = yes (t-≤ᵗ p)
...             | (no ¬p) = no λ{ (t-≤ᵗ t₁≤ₜt₂) → ¬p t₁≤ₜt₂}

_≟ᵗ_ : Decidable _≈ᵗ_
-∞   ≟ᵗ -∞  = yes -∞-refl
-∞   ≟ᵗ ∞   = no λ ()
-∞   ≟ᵗ t _ = no λ ()
∞    ≟ᵗ -∞  = no λ ()
t _  ≟ᵗ -∞  = no λ ()
∞    ≟ᵗ ∞   = yes ∞-refl
∞    ≟ᵗ t _ = no λ ()
t _  ≟ᵗ ∞   = no λ ()
t t₁ ≟ᵗ t t₂ with t₁ ≟ₜ t₂
...            | (yes p) = yes (t-refl p)
...            | (no ¬p) = no λ{ (t-refl p) → ¬p p }
