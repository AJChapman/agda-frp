open import Level
open import FRP.Time.DecOrderedGroup

-- Set up the namespace with the underlying time type as T, using a ₜ suffix,
-- and the ∞-extended time type as T̂, using a ᵗ suffix.
module FRP.Time
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open DecOrderedGroup Time public
  renaming
    ( Carrier to T
    ; _≈_ to _≈ₜ_
    ; _≤_ to _≤ₜ_
    ; _≤?_ to _≤?ₜ_
    ; _≟_ to _≟ₜ_
    ; _+_ to _+ₜ_
    ; ε to 0ₜ
    ; _⁻¹ to _⁻¹ₜ
    ; module Eq to Eqₜ
    ; reflexive to reflexiveₜ
    ; trans to transₜ
    ; antisym to antisymₜ
    ; total to totalₜ
    ; +-monoʳ-≤ to +-monoʳ-≤ₜ
    ; totalOrder to T-totalOrder
    )

open import FRP.Time.T+ Time public
  renaming
    ( _≈_ to _≈ᵗ_
    ; _≤_ to _≤ᵗ_
    ; _≤?_ to _≤?ᵗ_
    ; _≟_ to _≟ᵗ_
    ; ≈-refl to ≈ᵗ-refl
    ; ≈-sym to ≈ᵗ-sym
    ; ≈-trans to ≈ᵗ-trans
    ; reflexive to reflexiveᵗ
    ; ≤-trans to ≤ᵗ-trans
    ; antisym to antisymᵗ
    ; total to totalᵗ
    )
