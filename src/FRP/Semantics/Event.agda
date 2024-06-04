open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Semantics.Event
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import FRP.Semantics.Event.Type Time public
open import FRP.Semantics.Event.Raw Time public
