open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.E.Type
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import Data.List as List using (List)
open import Data.Product using (_,_; ∃)
open import Relation.Binary.Core using (_Preserves_⟶_)

open import FRP.T time using (T; _≤ₜ?_)
open import FRP.F time
  renaming (_<$>_ to _<$ᶠ>_)
  using (F; mapTime; F-totalOrder; F-decTotalOrder; NotAfter; notAfter?; F-<$>-Preserves-NotAfter; F-mapTime-Preserves-NotAfter)

private
  variable
    A B : Set a

-- Events' occurrences are at points in time relative to a common starting point,
-- and they are sorted by this time (earliest to latest).
-- Negative times are permissible, and may even make sense sometimes!
module _ where
  open import Data.List.Relation.Unary.Sorted.TotalOrder
  open import Data.List.Relation.Unary.Sorted.TotalOrder.Properties

  -- An `𝔼 A` is a sorted list of `F A`s
  𝔼 : Set a → Set (suc a ⊔ ℓ)
  𝔼 A = ∃ (Sorted (F-totalOrder A))

  merge : 𝔼 A → 𝔼 A → 𝔼 A
  merge {A} (e₁ , sorted₁) (e₂ , sorted₂) =
    List.merge notAfter? e₁ e₂ , merge⁺ (F-decTotalOrder A) sorted₁ sorted₂

  map : (f : F A → F B) → (f Preserves (NotAfter {A}) ⟶ (NotAfter {B})) → 𝔼 A → 𝔼 B
  map {A} {B} f p (e , sorted) = List.map f e , map⁺ (F-totalOrder A) (F-totalOrder B) p sorted

  infixl 4 _<$>_
  _<$>_ : (A → B) → 𝔼 A → 𝔼 B
  f <$> x = map (f <$ᶠ>_) (F-<$>-Preserves-NotAfter f) x

  mapTimes : (f : T → T) → (mapTime f Preserves NotAfter ⟶ NotAfter) → 𝔼 A → 𝔼 A
  mapTimes {A} f p (e , sorted) = List.map (mapTime f) e , map⁺ (F-totalOrder A) (F-totalOrder A) p sorted

