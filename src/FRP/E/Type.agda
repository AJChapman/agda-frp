open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.E.Type
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import Data.List as List using (List)
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive; Antisymmetric; Total; _⇒_)

open import FRP.T time using (T; module Eqₜ; _≈ₜ_; _≤ₜ_; _≤ₜ?_; totalOrderₜ)
open import Data.List.Relation.Unary.Sorted.TotalOrder totalOrderₜ

private
  variable
    A : Set a

infix 4 _≈ₜₓ_ _≤ₜₓ_ -- _≤?ₜₓ_ _≟ₜₓ_

data _≈ₜₓ_ : Rel (T × A) ℓ where
  reflₜₓ : ∀{t₁ t₂ : T} → {x y : A} → (t₁ ≈ₜ t₂) → (t₁ , x) ≈ₜₓ (t₂ , y)
-- (t₁ , _) ≈ₜₓ (t₂ , _) = t₁ ≈ₜ t₂

_≤ₜₓ_ : Rel (T × A) ℓ
(t₁ , _) ≤ₜₓ (t₂ , _) = t₁ ≤ₜ t₂

≈ₜₓ-refl : {A : Set a} → Reflexive (_≈ₜₓ_ {A})
≈ₜₓ-refl {A} {t₁ , x} = reflₜₓ Eqₜ.refl

≈ₜₓ-sym : Symmetric _≈ₜₓ_
≈ₜₓ-sym (reflₜₓ _) = reflₜₓ Eqₜ.sym
-- ≈ₜₓ-sym ((t₁ , _) ≈ₜₓ (t₂ , _)) = Eqₜ.sym (t₁ ≈ₜ t₂)

-- ≈ₜₓ-trans : Transitive _≈ₜₓ_
-- ≈ₜₓ-trans (reflₜₓ t₁ t₂) (reflₜₓ t₂ t₃) = reflₜₓ
-- -- ≈ₜₓ-trans ((t₁ , _) ≈ₜₓ (t₂ , _)) ((t₂ , _) ≈ₜₓ (t₃ , _)) = Eqₜ.trans (t₁ ≈ₜ t₂) (t₂ ≈ₜ t₃)

module T×-ordering {A : Set a} where
  open import Relation.Binary.Structures (_≈ₜₓ_ {A}) using (IsEquivalence; IsPreorder; IsPartialOrder; IsTotalOrder; IsDecTotalOrder)

  T×-isEquivalence : IsEquivalence
  T×-isEquivalence = record
    { refl = ≈ₜₓ-refl
    ; sym = ≈ₜₓ-sym
    -- ; trans = ≈ₜₓ-trans
    }

--   T×-isPreorder : IsPreorder _≤ₜₓ_
--   T×-isPreorder = record
--     { isEquivalence = T×-isEquivalence
--     ; reflexive = ≈ₜₓ-≤ₜₓ
--     ; trans = ≤ₜₓ-trans
--     }
-- 
--   T×-isPartialOrder : IsPartialOrder _≤ₜₓ_
--   T×-isPartialOrder = record
--     { isPreorder = T×-isPreorder
--     ; antisym = antisymᵗ
--     }
-- 
--   T×-isTotalOrder : IsTotalOrder _≤ₜₓ_
--   T×-isTotalOrder = record
--     { isPartialOrder = T×-isPartialOrder
--     ; total = ≤ₜₓ-total
--     }
-- 
--   T×-isDecTotalOrder : IsDecTotalOrder _≤ₜₓ_
--   T×-isDecTotalOrder = record
--     { isTotalOrder = T×-isTotalOrder
--     ; _≟_ = _≟ᵗ_
--     ; _≤?_ = _≤ₜₓ?_
--     }
-- 
--   T×-decTotalOrder : DecTotalOrder a ℓ ℓ
--   T×-decTotalOrder = record
--     { Carrier = T×
--     ; _≈_ = _≈ₜₓ_
--     ; _≤_ = _≤ₜₓ_
--     ; isDecTotalOrder = T×-isDecTotalOrder
--     }
-- 
-- open T××-ordering public
-- Events' occurrences are at points in time relative to a common starting point,
-- and they are sorted by this time (earliest to latest).
-- Negative times are permissible, and may even make sense sometimes!
𝔼 : Set a → Set a
-- 𝔼 A = Sorted (T × A)
𝔼 A = List (T × A)

merge : {A : Set a} → 𝔼 A → 𝔼 A → 𝔼 A
merge = List.merge (λ (t₁ , _) (t₂ , _) → t₁ ≤ₜ? t₂)

mapTimes : {A : Set a} → (T → T) → 𝔼 A → 𝔼 A
mapTimes f = List.map (λ (t₁ , x) → (f t₁ , x))

