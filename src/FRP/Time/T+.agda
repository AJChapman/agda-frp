open import Level
open import FRP.Time.DecOrderedGroup

-- Extend a time type to T̂ by adding -∞ and ∞
module FRP.Time.T+
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import Data.Sum using (_⊎_; inj₁; inj₂; map)
open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive; Antisymmetric; Total; _⇒_)
open import Relation.Binary.Bundles using (TotalOrder)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Decidable using (yes; no)

open DecOrderedGroup Time
  renaming
    ( Carrier to T
    ; _≈_ to _≈ₜ_
    ; _≤_ to _≤ₜ_
    ; _≤?_ to _≤?ₜ_
    ; _≟_ to _≟ₜ_
    ; ε to 0ₜ
    ; module Eq to Eqₜ
    ; reflexive to reflexiveₜ
    ; trans to transₜ
    ; antisym to antisymₜ
    ; total to totalₜ
    )

data T̂ : Set a where
  -∞ : T̂
  t̂  : T → T̂
  ∞  : T̂

infix 4 _≈_ _≤_ _≤?_ _≟_

data _≈_ : Rel T̂ (a ⊔ ℓ) where
  -∞-refl : -∞ ≈ -∞
  ∞-refl :   ∞ ≈  ∞
  t-refl : ∀{t₁ t₂ : T} → t₁ ≈ₜ t₂ → t̂ t₁ ≈ t̂ t₂

data _≤_ : Rel T̂ (a ⊔ ℓ) where
  -∞-≤ : ∀{t₂ : T̂} → -∞ ≤ t₂
  ≤-∞  : ∀{t₁ : T̂} → t₁ ≤ ∞
  t-≤  : ∀{t₁ t₂ : T} → t₁ ≤ₜ t₂ → t̂ t₁ ≤ t̂ t₂

0ᵗ : T̂
0ᵗ = t̂ 0ₜ

_≤?_ : Decidable _≤_
-∞   ≤?  _   = yes -∞-≤
_    ≤?  ∞   = yes  ≤-∞
∞    ≤? -∞   = no λ ()
t̂ t₁ ≤? -∞   = no λ ()
∞    ≤? t̂ t₂ = no λ ()
t̂ t₁ ≤? t̂ t₂ with t₁ ≤?ₜ t₂
...             | (yes p) = yes (t-≤ p)
...             | (no ¬p) = no λ{ (t-≤ t₁≤ₜt₂) → ¬p t₁≤ₜt₂}

_≟_ : Decidable _≈_
-∞   ≟ -∞  = yes -∞-refl
-∞   ≟ ∞   = no λ ()
-∞   ≟ t̂ _ = no λ ()
∞    ≟ -∞  = no λ ()
t̂ _  ≟ -∞  = no λ ()
∞    ≟ ∞   = yes ∞-refl
∞    ≟ t̂ _ = no λ ()
t̂ _  ≟ ∞   = no λ ()
t̂ t₁ ≟ t̂ t₂ with t₁ ≟ₜ t₂
...            | (yes p) = yes (t-refl p)
...            | (no ¬p) = no λ{ (t-refl p) → ¬p p }

≈-refl : Reflexive _≈_
≈-refl { -∞ } = -∞-refl
≈-refl {∞} = ∞-refl
≈-refl {t̂ t₁} = t-refl Eqₜ.refl

≈-sym : Symmetric _≈_
≈-sym (-∞-refl) = -∞-refl
≈-sym (∞-refl) = ∞-refl
≈-sym (t-refl tr) = t-refl (Eqₜ.sym tr)

≈-trans : Transitive _≈_
≈-trans -∞-refl -∞-refl = -∞-refl
≈-trans ∞-refl ∞-refl = ∞-refl
≈-trans (t-refl tr₁) (t-refl tr₂) = t-refl (Eqₜ.trans tr₁ tr₂)

reflexive : _≈_ ⇒ _≤_
reflexive (-∞-refl) = -∞-≤
reflexive ∞-refl = ≤-∞
reflexive (t-refl tr) = t-≤ (reflexiveₜ tr)

≤-trans : Transitive _≤_ -- ∀ {i j k} → i ≤ j → j ≤ k → i ≤ k
≤-trans (-∞-≤) _ = -∞-≤
≤-trans x ≤-∞ = ≤-∞
≤-trans (t-≤ x) (t-≤ y) = t-≤ (transₜ x y)

antisym : Antisymmetric _≈_ _≤_ -- ∀ {i j} → i ≤ j → j ≤ i → i ≈ j
antisym -∞-≤ -∞-≤ = -∞-refl
antisym ≤-∞ ≤-∞ = ∞-refl
antisym (t-≤ x) (t-≤ y) = t-refl (antisymₜ x y)

total : Total _≤_ -- ∀ x y → x ≤ y ⊎ y ≤ x
total -∞ _ = inj₁ -∞-≤
total (t̂ x) -∞ = inj₂ -∞-≤
total (t̂ x) (t̂ y) = map t-≤ t-≤ (totalₜ x y)
total (t̂ x) ∞ = inj₁ ≤-∞
total ∞ y = inj₂ ≤-∞

module T̂-ordering where
  open import Relation.Binary.Structures _≈_ using (IsEquivalence; IsPreorder; IsPartialOrder; IsTotalOrder; IsDecTotalOrder)

  T̂-isEquivalence : IsEquivalence
  T̂-isEquivalence = record
    { refl = ≈-refl
    ; sym = ≈-sym
    ; trans = ≈-trans
    }

  T̂-isPreorder : IsPreorder _≤_
  T̂-isPreorder = record
    { isEquivalence = T̂-isEquivalence
    ; reflexive = reflexive
    ; trans = ≤-trans
    }

  T̂-isPartialOrder : IsPartialOrder _≤_
  T̂-isPartialOrder = record
    { isPreorder = T̂-isPreorder
    ; antisym = antisym
    }

  T̂-isTotalOrder : IsTotalOrder _≤_
  T̂-isTotalOrder = record
    { isPartialOrder = T̂-isPartialOrder
    ; total = total
    }

  T̂-totalOrder : TotalOrder a (a ⊔ ℓ) (a ⊔ ℓ)
  T̂-totalOrder = record
    { Carrier = T̂
    ; _≈_ = _≈_
    ; _≤_ = _≤_
    ; isTotalOrder = T̂-isTotalOrder
    }

  T̂-isDecTotalOrder : IsDecTotalOrder _≤_
  T̂-isDecTotalOrder = record
    { isTotalOrder = T̂-isTotalOrder
    ; _≟_ = _≟_
    ; _≤?_ = _≤?_
    }

open T̂-ordering public
