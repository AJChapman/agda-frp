module FRP.E
  ( T : Set
  ) where

open import Data.List using (List)
open import Data.Product using (_×_)

open import FRP.T (T) using (T̂) public

-- Events occur at certain points in time
E : Set → Set
E A = List (T̂ × A)
