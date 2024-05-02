module FRP
  ( T : Set -- TODO: T should be totally ordered
  ) where

open import Data.List using (List)
open import Data.Product using (_×_)

Bₐ : {A : Set} → Set
Bₐ {A} = T → A

Eₐ : {A : Set} → Set
Eₐ {A} = List (T × A)
