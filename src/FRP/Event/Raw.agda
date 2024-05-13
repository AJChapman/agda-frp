open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.Event.Raw
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import FRP.Event.Type time

open import Algebra using (RawMonoid)
open import Data.List using ([]; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_)

monoid : Set a → RawMonoid a a
monoid A = record
  { Carrier = Event A
  ; _≈_ = _≡_
  ; _∙_ = _++_
  ; ε = []
  }
