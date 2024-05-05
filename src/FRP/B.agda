module FRP.B
  ( T : Set
  ) where

open import Function using (id)

-- Behaviours are values which vary over time
B : Set → Set
B A = T → A

time : B T
time = id
