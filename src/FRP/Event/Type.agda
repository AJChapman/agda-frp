open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.Event.Type
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import Data.List using (List)
open import Data.Product using (_×_)
open import Function using (id)

open import FRP.E time

-- This is our event implementation.
-- For now it's identical to the denotation, but this
-- will change as we develop a more efficient implementation.
Event : Set a → Set a
Event A = List (T̂ × A)

-- This maps from the event implementation to its denotation.
occs : {A : Set a} → Event A → 𝔼 A
occs = id
