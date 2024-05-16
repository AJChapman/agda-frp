open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.Event
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import FRP.Event.Type time public
open import FRP.Event.Raw time public
open import FRP.Event.Laws time public
