module FRP.Event
  ( T : Set
  ) where

open import Data.List using (List)
open import Data.Product using (_×_)
open import Function using (id)

open import FRP.E (T)

-- This is our event implementation.
-- For now it's identical to the denotation, but this
-- will change as we develop a more efficient implementation.
Event : Set → Set
Event A = List (T̂ × A)

-- This maps from the event implementation to its denotation.
occs : {A : Set} → Event A → E A
occs = id
