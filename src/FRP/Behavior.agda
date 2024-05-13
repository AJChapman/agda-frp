open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.Behavior
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import Function using (id; _∘_; const)

open import FRP.Behavior.Type time
open import FRP.Behavior.Laws time

open import FRP.B time

time : Behavior T
time = id
