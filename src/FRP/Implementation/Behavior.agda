open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Implementation.Behavior
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import Function using (id; _∘_; const)

open import FRP.Time Time
open import FRP.Implementation.Behavior.Type Time
open import FRP.Implementation.Behavior.Raw Time
open import FRP.Implementation.Behavior.Laws Time

timeᵇ : Behavior T
timeᵇ = id
