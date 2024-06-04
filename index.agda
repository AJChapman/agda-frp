open import Level
open import FRP.Time.DecOrderedGroup

module index
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import FRP.Time Time
open import FRP.Semantics.Behavior Time
open import FRP.Semantics.Future Time
open import FRP.Semantics.Event Time
open import FRP.Implementation.Behavior Time
open import FRP.Implementation.Event Time
