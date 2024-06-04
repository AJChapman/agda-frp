open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Semantics.Behavior
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import FRP.Semantics.Behavior.Type Time public
open import FRP.Semantics.Behavior.Raw Time public
open import FRP.Semantics.Behavior.Laws Time public
