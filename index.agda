open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module index
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import FRP.T time
open import FRP.B time
open import FRP.Behavior time
open import FRP.E time
open import FRP.Event time
