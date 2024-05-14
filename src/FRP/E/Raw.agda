open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.E.Raw
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import FRP.E.Type time

open import Algebra using (RawMonoid)
open import Data.List using ([]; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_)

monoid : Set a → RawMonoid a a
monoid A = record
  { Carrier = 𝔼 A
  ; _≈_ = _≡_
  ; _∙_ = merge
  ; ε = []
  }
