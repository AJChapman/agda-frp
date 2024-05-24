open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.T
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import Data.Sum using (_⊎_; inj₁; inj₂; map)
open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive; Antisymmetric; Total; _⇒_)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Decidable using (yes; no)

open DecTotalOrder time renaming
  ( Carrier to T
  ; _≈_ to _≈ₜ_
  ; module Eq to Eqₜ
  ; _≤_ to _≤ₜ_
  ; _≤?_ to _≤ₜ?_
  ; _≟_ to _≟ₜ_
  ; reflexive to reflexiveₜ
  ; trans to transₜ
  ; antisym to antisymₜ
  ; totalOrder to totalOrderₜ
  ; total to ≤ₜ-total
  ) using () public

data T̂ : Set a where
  -∞ : T̂
  t  : T → T̂
  ∞  : T̂

infix 4 _≈ᵗ_ _≤ᵗ_ _≤ᵗ?_ _≟ᵗ_

data _≈ᵗ_ : Rel T̂ ℓ where
  -∞-refl : -∞ ≈ᵗ -∞
  ∞-refl :   ∞ ≈ᵗ  ∞
  t-refl : ∀{t₁ t₂ : T} → t₁ ≈ₜ t₂ → t t₁ ≈ᵗ t t₂

data _≤ᵗ_ : Rel T̂ ℓ where
  -∞-≤ᵗ : ∀{t₂ : T̂} → -∞ ≤ᵗ t₂
  ≤ᵗ-∞  : ∀{t₁ : T̂} → t₁ ≤ᵗ ∞
  t-≤ᵗ  : ∀{t₁ t₂ : T} → t₁ ≤ₜ t₂ → t t₁ ≤ᵗ t t₂

_≤ᵗ?_ : Decidable _≤ᵗ_
-∞   ≤ᵗ?  _   = yes -∞-≤ᵗ
_    ≤ᵗ?  ∞   = yes  ≤ᵗ-∞
∞    ≤ᵗ? -∞   = no λ ()
t t₁ ≤ᵗ? -∞   = no λ ()
∞    ≤ᵗ? t t₂ = no λ ()
t t₁ ≤ᵗ? t t₂ with t₁ ≤ₜ? t₂
...             | (yes p) = yes (t-≤ᵗ p)
...             | (no ¬p) = no λ{ (t-≤ᵗ t₁≤ₜt₂) → ¬p t₁≤ₜt₂}

_≟ᵗ_ : Decidable _≈ᵗ_
-∞   ≟ᵗ -∞  = yes -∞-refl
-∞   ≟ᵗ ∞   = no λ ()
-∞   ≟ᵗ t _ = no λ ()
∞    ≟ᵗ -∞  = no λ ()
t _  ≟ᵗ -∞  = no λ ()
∞    ≟ᵗ ∞   = yes ∞-refl
∞    ≟ᵗ t _ = no λ ()
t _  ≟ᵗ ∞   = no λ ()
t t₁ ≟ᵗ t t₂ with t₁ ≟ₜ t₂
...            | (yes p) = yes (t-refl p)
...            | (no ¬p) = no λ{ (t-refl p) → ¬p p }

≈ᵗ-refl : Reflexive _≈ᵗ_
≈ᵗ-refl { -∞ } = -∞-refl
≈ᵗ-refl {∞} = ∞-refl
≈ᵗ-refl {t t₁} = t-refl Eqₜ.refl

≈ᵗ-sym : Symmetric _≈ᵗ_
≈ᵗ-sym (-∞-refl) = -∞-refl
≈ᵗ-sym (∞-refl) = ∞-refl
≈ᵗ-sym (t-refl tr) = t-refl (Eqₜ.sym tr)

≈ᵗ-trans : Transitive _≈ᵗ_
≈ᵗ-trans -∞-refl -∞-refl = -∞-refl
≈ᵗ-trans ∞-refl ∞-refl = ∞-refl
≈ᵗ-trans (t-refl tr₁) (t-refl tr₂) = t-refl (Eqₜ.trans tr₁ tr₂)

≈ᵗ-≤ᵗ : _≈ᵗ_ ⇒ _≤ᵗ_
≈ᵗ-≤ᵗ (-∞-refl) = -∞-≤ᵗ
≈ᵗ-≤ᵗ ∞-refl = ≤ᵗ-∞
≈ᵗ-≤ᵗ (t-refl tr) = t-≤ᵗ (reflexiveₜ tr)

≤ᵗ-trans : Transitive _≤ᵗ_ -- ∀ {i j k} → i ≤ᵗ j → j ≤ᵗ k → i ≤ᵗ k
≤ᵗ-trans (-∞-≤ᵗ) _ = -∞-≤ᵗ
≤ᵗ-trans x ≤ᵗ-∞ = ≤ᵗ-∞
≤ᵗ-trans (t-≤ᵗ x) (t-≤ᵗ y) = t-≤ᵗ (transₜ x y)

antisymᵗ : Antisymmetric _≈ᵗ_ _≤ᵗ_ -- ∀ {i j} → i ≤ᵗ j → j ≤ᵗ i → i ≈ᵗ j
antisymᵗ -∞-≤ᵗ -∞-≤ᵗ = -∞-refl
antisymᵗ ≤ᵗ-∞ ≤ᵗ-∞ = ∞-refl
antisymᵗ (t-≤ᵗ x) (t-≤ᵗ y) = t-refl (antisymₜ x y)

≤ᵗ-total : Total _≤ᵗ_ -- ∀ x y → x ≤ᵗ y ⊎ y ≤ᵗ x
≤ᵗ-total -∞ _ = inj₁ -∞-≤ᵗ
≤ᵗ-total (t x) -∞ = inj₂ -∞-≤ᵗ
≤ᵗ-total (t x) (t y) = map t-≤ᵗ t-≤ᵗ (≤ₜ-total x y)
≤ᵗ-total (t x) ∞ = inj₁ ≤ᵗ-∞
≤ᵗ-total ∞ y = inj₂ ≤ᵗ-∞

module T̂-ordering where
  open import Relation.Binary.Structures _≈ᵗ_ using (IsEquivalence; IsPreorder; IsPartialOrder; IsTotalOrder; IsDecTotalOrder)

  T̂-isEquivalence : IsEquivalence
  T̂-isEquivalence = record
    { refl = ≈ᵗ-refl
    ; sym = ≈ᵗ-sym
    ; trans = ≈ᵗ-trans
    }

  T̂-isPreorder : IsPreorder _≤ᵗ_
  T̂-isPreorder = record
    { isEquivalence = T̂-isEquivalence
    ; reflexive = ≈ᵗ-≤ᵗ
    ; trans = ≤ᵗ-trans
    }

  T̂-isPartialOrder : IsPartialOrder _≤ᵗ_
  T̂-isPartialOrder = record
    { isPreorder = T̂-isPreorder
    ; antisym = antisymᵗ
    }

  T̂-isTotalOrder : IsTotalOrder _≤ᵗ_
  T̂-isTotalOrder = record
    { isPartialOrder = T̂-isPartialOrder
    ; total = ≤ᵗ-total
    }

  T̂-isDecTotalOrder : IsDecTotalOrder _≤ᵗ_
  T̂-isDecTotalOrder = record
    { isTotalOrder = T̂-isTotalOrder
    ; _≟_ = _≟ᵗ_
    ; _≤?_ = _≤ᵗ?_
    }

  T̂-decTotalOrder : DecTotalOrder a ℓ ℓ
  T̂-decTotalOrder = record
    { Carrier = T̂
    ; _≈_ = _≈ᵗ_
    ; _≤_ = _≤ᵗ_
    ; isDecTotalOrder = T̂-isDecTotalOrder
    }

open T̂-ordering public
