open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.B
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import FRP.B.Type time public
open import FRP.B.Raw time public
open import FRP.B.Laws time public
