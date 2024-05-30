open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.F
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import Data.Product using (_×_; _,_; ∃)
open import Data.Sum using (_⊎_; map)
open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive; Antisymmetric; Total; _⇒_)
open import Relation.Binary.Bundles using (TotalOrder)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary.Decidable using (yes; no)

open import FRP.T time using (T; module Eqₜ; _≈ₜ_; _≟ₜ_; _≤ₜ_; _≤ₜ?_; totalOrderₜ; reflexiveₜ; transₜ; antisymₜ; ≤ₜ-total)

private
  variable
    A B : Set a

-- Future values are a pair of time and value
F : Set a → Set a
F A = T × A

infixl 4 _<$>_
_<$>_ : (A → B) → F A → F B
f <$> (t₁ , x) = t₁ , f x

mapTime : (T → T) → F A → F A
mapTime f (t₁ , x) = f t₁ , x

data Simultaneous : Rel (F A) (suc a ⊔ ℓ) where
  sim : ∀{t₁ t₂ : T} → {x y : A} → (t₁ ≈ₜ t₂) → Simultaneous (t₁ , x) (t₂ , y)

data NotAfter : Rel (F A) (suc a ⊔ ℓ) where
  notAfter : ∀{t₁ t₂ : T} → {x y : A} → (t₁ ≤ₜ t₂) → NotAfter (t₁ , x) (t₂ , y)

simultaneous? : Decidable (Simultaneous {A})
simultaneous? (t₁ , x) (t₂ , y) with t₁ ≟ₜ t₂
...                               | (yes t₁≈t₂) = yes (sim t₁≈t₂)
...                               | (no t₁¬≈t₂) = no λ{ (sim t₁≈t₂) → t₁¬≈t₂ t₁≈t₂}

notAfter? : Decidable (NotAfter {A})
notAfter? (t₁ , x) (t₂ , y) with t₁ ≤ₜ? t₂
...                           | (yes t₁≤t₂) = yes (notAfter t₁≤t₂)
...                           | (no ¬t₁≤t₂) = no λ{ (notAfter t₁≤t₂) → ¬t₁≤t₂ t₁≤t₂ }

sim-refl : Reflexive (Simultaneous {A})
sim-refl {A} {t₁ , x} = sim Eqₜ.refl

sim-sym : Symmetric (Simultaneous {A})
sim-sym {A} (sim t₁≈ₜt₂) = sim (Eqₜ.sym t₁≈ₜt₂)

sim-trans : Transitive (Simultaneous {A})
sim-trans (sim t₁≈t₂) (sim t₂≈t₃) = sim (Eqₜ.trans t₁≈t₂ t₂≈t₃)

sim-notAfter : Simultaneous {A} ⇒ NotAfter {A}
sim-notAfter (sim t₁≈t₂) = notAfter (reflexiveₜ t₁≈t₂)

sim-notAfter-trans : Transitive (NotAfter {A})
sim-notAfter-trans (notAfter t₁≤t₂) (notAfter t₂≤t₃) = notAfter (transₜ t₁≤t₂ t₂≤t₃)

sim-notAfter-antisym : Antisymmetric (Simultaneous {A}) (NotAfter {A})
sim-notAfter-antisym (notAfter i≤j) (notAfter j≤i) = sim (antisymₜ i≤j j≤i)

notAfter-total : Total (NotAfter {A}) -- ∀ x y → notAfter x y ⊎ notAfter y x
notAfter-total (t₁ , x) (t₂ , y) = map notAfter notAfter (≤ₜ-total t₁ t₂)

module F-ordering (A : Set a) where
  open import Relation.Binary.Structures (Simultaneous {A})
    using (IsEquivalence; IsPreorder; IsPartialOrder; IsTotalOrder; IsDecTotalOrder)

  F-isEquivalence : IsEquivalence
  F-isEquivalence = record
    { refl = sim-refl
    ; sym = sim-sym
    ; trans = sim-trans
    }

  F-isPreorder : IsPreorder NotAfter
  F-isPreorder = record
    { isEquivalence = F-isEquivalence
    ; reflexive = sim-notAfter
    ; trans = sim-notAfter-trans
    }

  F-isPartialOrder : IsPartialOrder NotAfter
  F-isPartialOrder = record
    { isPreorder = F-isPreorder
    ; antisym = sim-notAfter-antisym
    }

  F-isTotalOrder : IsTotalOrder NotAfter
  F-isTotalOrder = record
    { isPartialOrder = F-isPartialOrder
    ; total = notAfter-total
    }

  F-totalOrder : TotalOrder a (suc a ⊔ ℓ) (suc a ⊔ ℓ)
  F-totalOrder = record
    { Carrier = F A
    ; _≈_ = Simultaneous {A}
    ; _≤_ = NotAfter {A}
    ; isTotalOrder = F-isTotalOrder
    }

  F-isDecTotalOrder : IsDecTotalOrder NotAfter
  F-isDecTotalOrder = record
    { isTotalOrder = F-isTotalOrder
    ; _≟_ = simultaneous?
    ; _≤?_ = notAfter?
    }

  F-decTotalOrder : DecTotalOrder a (suc a ⊔ ℓ) (suc a ⊔ ℓ)
  F-decTotalOrder = record
    { Carrier = F A
    ; _≈_ = Simultaneous {A}
    ; _≤_ = NotAfter {A}
    ; isDecTotalOrder = F-isDecTotalOrder
    }

open F-ordering public

F-<$>-Preserves-NotAfter : (f : A → B) → (f <$>_) Preserves (NotAfter {A}) ⟶ (NotAfter {B}) -- ∀ {x y : A} → NotAfter x y → NotAfter (f x) (f y)
F-<$>-Preserves-NotAfter f (notAfter x≤y) = notAfter x≤y

F-mapTime-Preserves-NotAfter : (f : T → T) → f Preserves _≤ₜ_ ⟶ _≤ₜ_ → mapTime f Preserves (NotAfter {A}) ⟶ (NotAfter {A})
F-mapTime-Preserves-NotAfter f p (notAfter x≤y) = notAfter (p x≤y)