module FRP.Time.DecOrderedGroup where

open import Level using (suc; _⊔_)

open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Structures using (IsGroup)
open import Relation.Binary.Core using (Rel; _Preserves_⟶_)
open import Relation.Binary.Bundles using (TotalOrder; DecPoset)
open import Relation.Binary.Structures using (IsDecTotalOrder; IsDecEquivalence)

-- This is the interface that any underlying time type must implement:
-- In brief, it must be ordered and be a group (i.e. have a 0, addition and subtraction).
record DecOrderedGroup a ℓ₁ ℓ₂ : Set (suc (a ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≤_
  infixl 6 _+_
  field
    Carrier : Set a
    _≈_ : Rel Carrier ℓ₁
    _≤_ : Rel Carrier ℓ₂
    isDecTotalOrder : IsDecTotalOrder _≈_ _≤_
    _+_ : Op₂ Carrier
    ε : Carrier
    _⁻¹ : Op₁ Carrier
    isGroup : IsGroup _≈_ _+_ ε _⁻¹
    +-monoʳ-≤ : ∀ c → (c +_) Preserves _≤_ ⟶ _≤_

  -- The below is boilerplate borrowed from DecTotalOrder
  private module DTO = IsDecTotalOrder isDecTotalOrder

  open DTO public
    using (_≟_; _≤?_; isTotalOrder; isDecPartialOrder)

  totalOrder : TotalOrder a ℓ₁ ℓ₂
  totalOrder = record
    { isTotalOrder = isTotalOrder
    }

  open TotalOrder totalOrder public
    hiding (Carrier; _≈_; _≤_; isTotalOrder; module Eq)

  decPoset : DecPoset a ℓ₁ ℓ₂
  decPoset = record
    { isDecPartialOrder = isDecPartialOrder
    }

  open DecPoset decPoset public
    using (module Eq)
 