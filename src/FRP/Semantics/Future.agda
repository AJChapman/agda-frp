open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Semantics.Future
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import Data.Product using (_×_; _,_; ∃)
open import Data.Sum using (_⊎_; map)
open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive; Antisymmetric; Total; _⇒_)
open import Relation.Binary.Bundles using (TotalOrder; DecTotalOrder)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary.Decidable using (yes; no)

open import FRP.Time Time

private
  variable
    A B : Set a

-- Future values are a pair of time and value
Future : Set a → Set a
Future A = T̂ × A

infixl 4 _<$>_
_<$>_ : (A → B) → Future A → Future B
f <$> (t₁ , x) = t₁ , f x

mapTime : (T̂ → T̂) → Future A → Future A
mapTime f (t₁ , x) = f t₁ , x

data _≈ᵗ,_ {A : Set a} : Rel (Future A) (a ⊔ ℓ) where
  sim : ∀ {t₁ t₂} {x y : A} (t₁≈t₂ : t₁ ≈ᵗ t₂) → (t₁ , x) ≈ᵗ, (t₂ , y)

data _≤ᵗ,_ {A : Set a} : Rel (Future A) (a ⊔ ℓ) where
  notAfter : ∀{t₁ t₂} {x y : A} → (t₁≤t₂ : t₁ ≤ᵗ t₂) → (t₁ , x) ≤ᵗ, (t₂ , y)

_≟ᵗ,_ : Decidable (_≈ᵗ,_ {A})
_≟ᵗ,_ (t₁ , x) (t₂ , y) with t₁ ≟ᵗ t₂
...                               | (yes t₁≈t₂) = yes (sim t₁≈t₂)
...                               | (no t₁¬≈t₂) = no λ{ (sim t₁≈t₂) → t₁¬≈t₂ t₁≈t₂}

_≤?ᵗ,_ : Decidable (_≤ᵗ,_ {A})
_≤?ᵗ,_ (t₁ , x) (t₂ , y) with t₁ ≤?ᵗ t₂
...                           | (yes t₁≤t₂) = yes (notAfter t₁≤t₂)
...                           | (no ¬t₁≤t₂) = no λ{ (notAfter t₁≤t₂) → ¬t₁≤t₂ t₁≤t₂ }

sim-refl : Reflexive (_≈ᵗ,_ {A})
sim-refl {A} {t₁ , x} = sim ≈ᵗ-refl

sim-sym : Symmetric (_≈ᵗ,_ {A})
sim-sym {A} (sim t₁≈t₂) = sim (≈ᵗ-sym t₁≈t₂)

sim-trans : Transitive (_≈ᵗ,_ {A})
sim-trans (sim t₁≈t₂) (sim t₂≈t₃) = sim (≈ᵗ-trans t₁≈t₂ t₂≈t₃)

sim-≤ᵗ, : _≈ᵗ,_ {A} ⇒ _≤ᵗ,_ {A}
sim-≤ᵗ, (sim t₁≈t₂) = notAfter (reflexiveᵗ t₁≈t₂)

sim-≤ᵗ,-trans : Transitive (_≤ᵗ,_ {A})
sim-≤ᵗ,-trans (notAfter t₁≤t₂) (notAfter t₂≤t₃) = notAfter (≤ᵗ-trans t₁≤t₂ t₂≤t₃)

sim-≤ᵗ,-antisym : Antisymmetric (_≈ᵗ,_ {A}) (_≤ᵗ,_ {A})
sim-≤ᵗ,-antisym (notAfter i≤j) (notAfter j≤i) = sim (antisymᵗ i≤j j≤i)

≤ᵗ,-total : Total (_≤ᵗ,_ {A}) -- ∀ x y → x ≤ᵗ, y ⊎ y ≤ᵗ,x
≤ᵗ,-total (t₁ , x) (t₂ , y) = map notAfter notAfter (totalᵗ t₁ t₂)

module future-ordering (A : Set a) where
  open import Relation.Binary.Structures (_≈ᵗ,_ {A})
    using (IsEquivalence; IsPreorder; IsPartialOrder; IsTotalOrder; IsDecTotalOrder)

  future-isEquivalence : IsEquivalence
  future-isEquivalence = record
    { refl = sim-refl
    ; sym = sim-sym
    ; trans = sim-trans
    }

  future-isPreorder : IsPreorder _≤ᵗ,_
  future-isPreorder = record
    { isEquivalence = future-isEquivalence
    ; reflexive = sim-≤ᵗ,
    ; trans = sim-≤ᵗ,-trans
    }

  future-isPartialOrder : IsPartialOrder _≤ᵗ,_
  future-isPartialOrder = record
    { isPreorder = future-isPreorder
    ; antisym = sim-≤ᵗ,-antisym
    }

  future-isTotalOrder : IsTotalOrder _≤ᵗ,_
  future-isTotalOrder = record
    { isPartialOrder = future-isPartialOrder
    ; total = ≤ᵗ,-total
    }

  future-totalOrder : TotalOrder a (a ⊔ ℓ) (a ⊔ ℓ)
  future-totalOrder = record
    { Carrier = Future A
    ; _≈_ = _≈ᵗ,_ {A}
    ; _≤_ = _≤ᵗ,_ {A}
    ; isTotalOrder = future-isTotalOrder
    }

  future-isDecTotalOrder : IsDecTotalOrder _≤ᵗ,_
  future-isDecTotalOrder = record
    { isTotalOrder = future-isTotalOrder
    ; _≟_ = _≟ᵗ,_
    ; _≤?_ = _≤?ᵗ,_
    }

  future-decTotalOrder : DecTotalOrder a (a ⊔ ℓ) (a ⊔ ℓ)
  future-decTotalOrder = record
    { Carrier = Future A
    ; _≈_ = _≈ᵗ,_ {A}
    ; _≤_ = _≤ᵗ,_ {A}
    ; isDecTotalOrder = future-isDecTotalOrder
    }

open future-ordering public

future-<$>-Preserves-≤ᵗ, : (f : A → B) → (f <$>_) Preserves _≤ᵗ,_ ⟶ _≤ᵗ,_ -- ∀ {x y : A} →  x ≤ᵗ, y → f x ≤ᵗ, f y
future-<$>-Preserves-≤ᵗ, f (notAfter x≤y) = notAfter x≤y

future-mapTime-Preserves-≤ᵗ, : (f : T̂ → T̂) → f Preserves _≤ᵗ_ ⟶ _≤ᵗ_ → mapTime f Preserves _≤ᵗ,_ ⟶ _≤ᵗ,_ {A}
future-mapTime-Preserves-≤ᵗ, f p (notAfter x≤y) = notAfter (p x≤y)