open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.E
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import FRP.E.Type time public
