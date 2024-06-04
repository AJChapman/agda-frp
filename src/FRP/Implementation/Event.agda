open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Implementation.Event
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import FRP.Implementation.Event.Type Time public
open import FRP.Implementation.Event.Raw Time public
open import FRP.Implementation.Event.Laws Time public
