open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Semantics.Future.Type
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Sum using (_⊎_; map)
open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive; Antisymmetric; Total; _⇒_)
open import Relation.Binary.Bundles using (TotalOrder; DecTotalOrder)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary.Decidable using (yes; no)

open DecOrderedGroup Time
  renaming
    ( Carrier to T
    ; _≈_ to _≈ₜ_
    ; _≤_ to _≤ₜ_
    ; _≟_ to _≟ₜ_
    ; _≤?_ to _≤?ₜ_
    ; ε to 0ₜ
    ; module Eq to Eqₜ
    ; reflexive to reflexiveₜ
    ; trans to transₜ
    ; antisym to antisymₜ
    ; total to totalₜ
    )
  using ()

private
  variable
    A B : Set a

-- Future values are a pair of time and value
Future : Set a → Set a
Future A = T × A

0ₜ, : A → Future A
0ₜ, x = 0ₜ , x

infixl 4 _<$>_
_<$>_ : (A → B) → Future A → Future B
f <$> (t₁ , x) = t₁ , f x

mapTime : (T → T) → Future A → Future A
mapTime f (t₁ , x) = f t₁ , x

data _≈_ {A : Set a} : Rel (Future A) (a ⊔ ℓ) where
  sim : ∀ {t₁ t₂} {x y : A} (t₁≈t₂ : t₁ ≈ₜ t₂) → (t₁ , x) ≈ (t₂ , y)

data _≤_ {A : Set a} : Rel (Future A) (a ⊔ ℓ) where
  notAfter : ∀{t₁ t₂} {x y : A} → (t₁≤t₂ : t₁ ≤ₜ t₂) → (t₁ , x) ≤ (t₂ , y)

_≟_ : Decidable (_≈_ {A})
_≟_ (t₁ , x) (t₂ , y) with t₁ ≟ₜ t₂
...                               | (yes t₁≈t₂) = yes (sim t₁≈t₂)
...                               | (no t₁¬≈t₂) = no λ{ (sim t₁≈t₂) → t₁¬≈t₂ t₁≈t₂}

_≤?_ : Decidable (_≤_ {A})
_≤?_ (t₁ , x) (t₂ , y) with t₁ ≤?ₜ t₂
...                           | (yes t₁≤t₂) = yes (notAfter t₁≤t₂)
...                           | (no ¬t₁≤t₂) = no λ{ (notAfter t₁≤t₂) → ¬t₁≤t₂ t₁≤t₂ }

sim-refl : Reflexive (_≈_ {A})
sim-refl {A} {t₁ , x} = sim (Eqₜ.reflexive refl)

sim-sym : Symmetric (_≈_ {A})
sim-sym {A} (sim t₁≈t₂) = sim (Eqₜ.sym t₁≈t₂)

sim-trans : Transitive (_≈_ {A})
sim-trans (sim t₁≈t₂) (sim t₂≈t₃) = sim (Eqₜ.trans t₁≈t₂ t₂≈t₃)

sim-≤ : _≈_ {A} ⇒ _≤_ {A}
sim-≤ (sim t₁≈t₂) = notAfter (reflexiveₜ t₁≈t₂)

sim-≤-trans : Transitive (_≤_ {A})
sim-≤-trans (notAfter t₁≤t₂) (notAfter t₂≤t₃) = notAfter (transₜ t₁≤t₂ t₂≤t₃)

sim-≤-antisym : Antisymmetric (_≈_ {A}) (_≤_ {A})
sim-≤-antisym (notAfter i≤j) (notAfter j≤i) = sim (antisymₜ i≤j j≤i)

≤-total : Total (_≤_ {A}) -- ∀ x y → x ≤ y ⊎ y ≤ x
≤-total (t₁ , x) (t₂ , y) = map notAfter notAfter (totalₜ t₁ t₂)

module future-ordering (A : Set a) where
  open import Relation.Binary.Structures (_≈_ {A})
    using (IsEquivalence; IsPreorder; IsPartialOrder; IsTotalOrder; IsDecTotalOrder)

  future-isEquivalence : IsEquivalence
  future-isEquivalence = record
    { refl = sim-refl
    ; sym = sim-sym
    ; trans = sim-trans
    }

  future-isPreorder : IsPreorder _≤_
  future-isPreorder = record
    { isEquivalence = future-isEquivalence
    ; reflexive = sim-≤
    ; trans = sim-≤-trans
    }

  future-isPartialOrder : IsPartialOrder _≤_
  future-isPartialOrder = record
    { isPreorder = future-isPreorder
    ; antisym = sim-≤-antisym
    }

  future-isTotalOrder : IsTotalOrder _≤_
  future-isTotalOrder = record
    { isPartialOrder = future-isPartialOrder
    ; total = ≤-total
    }

  future-totalOrder : TotalOrder a (a ⊔ ℓ) (a ⊔ ℓ)
  future-totalOrder = record
    { Carrier = Future A
    ; _≈_ = _≈_ {A}
    ; _≤_ = _≤_ {A}
    ; isTotalOrder = future-isTotalOrder
    }

  future-isDecTotalOrder : IsDecTotalOrder _≤_
  future-isDecTotalOrder = record
    { isTotalOrder = future-isTotalOrder
    ; _≟_ = _≟_
    ; _≤?_ = _≤?_
    }

  future-decTotalOrder : DecTotalOrder a (a ⊔ ℓ) (a ⊔ ℓ)
  future-decTotalOrder = record
    { Carrier = Future A
    ; _≈_ = _≈_ {A}
    ; _≤_ = _≤_ {A}
    ; isDecTotalOrder = future-isDecTotalOrder
    }

open future-ordering public

future-<$>-Preserves-≤ : (f : A → B) → (f <$>_) Preserves _≤_ ⟶ _≤_ -- ∀ {x y : A} →  x ≤ y → f x ≤ f y
future-<$>-Preserves-≤ f (notAfter x≤y) = notAfter x≤y

future-mapTime-Preserves-≤ : (f : T → T) → f Preserves _≤ₜ_ ⟶ _≤ₜ_ → mapTime f Preserves _≤_ ⟶ _≤_ {A}
future-mapTime-Preserves-≤ f p (notAfter x≤y) = notAfter (p x≤y)