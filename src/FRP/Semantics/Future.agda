open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Semantics.Future
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import FRP.Semantics.Future.Type Time public
  renaming
    ( _≈_ to _≈ₜ,_
    ; _≤_ to _≤ₜ,_
    ; _≟_ to _≟ₜ,_
    ; _≤?_ to _≤?ₜ,_
    ; sim-refl to sim-reflₜ,
    ; sim-sym to sim-symₜ,
    ; sim-trans to sim-transₜ,
    ; sim-≤ to sim-≤ₜ,
    ; sim-≤-trans to sim-≤ₜ,-trans
    ; sim-≤-antisym to sim-≤ₜ,-antisym
    ; ≤-total to ≤-totalₜ,
    ; future-<$>-Preserves-≤ to future-<$>-Preserves-≤ₜ,
    ; future-mapTime-Preserves-≤ to future-mapTime-Preserves-≤ₜ,
    ; _<$>_ to _<$>ₜ,_
    )