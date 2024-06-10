open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Semantics.Event.Laws
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import Relation.Binary.Core using (_Preserves_⟶_)

open import FRP.Time Time
open import FRP.Semantics.Event.Type Time
open import FRP.Semantics.Future Time
  renaming (_<$>_ to _<$ᶠ>_)
  using (Future; mapTime; future-totalOrder; future-decTotalOrder; _≤ᵗ,_; future-mapTime-Preserves-≤ᵗ,)

private
  variable
    A B : Set a

module event-futures-sorted (A B : Set a) where
  open import Data.List.Relation.Unary.Sorted.TotalOrder (future-totalOrder A)
    renaming (Sorted to Sortedᵃ)
    using ()
  open import Data.List.Relation.Unary.Sorted.TotalOrder (future-totalOrder B)
    renaming (Sorted to Sortedᵇ)
    using ()
  open import Data.List.Relation.Unary.Sorted.TotalOrder.Properties
  open import Data.List.Relation.Unary.Linked as Linked using ([-])

  empty-sorted : Sortedᵃ empty
  empty-sorted = Linked.[]

  now-sorted : ∀{x : A} → Sortedᵃ (now x)
  now-sorted = [-]

  merge-preserves-sorted : ∀{e₁ e₂ : Event A} → Sortedᵃ e₁ → Sortedᵃ e₂ → Sortedᵃ (merge e₁ e₂)
  merge-preserves-sorted s₁ s₂ = merge⁺ (future-decTotalOrder A) s₁ s₂

  map-preserves-sorted : ∀{e : Event A} → (f : Future A → Future B) → (p : f Preserves _≤ᵗ,_ ⟶ _≤ᵗ,_) → Sortedᵃ e → Sortedᵇ (map f p e)
  map-preserves-sorted f p s =  map⁺ (future-totalOrder A) (future-totalOrder B) p s

  mapTimes-preserves-sorted : ∀{e : Event A} (f : T̂ → T̂) → (p : f Preserves _≤ᵗ_ ⟶ _≤ᵗ_) → Sortedᵃ e → Sortedᵃ (mapTimes f p e)
  mapTimes-preserves-sorted f p s = map⁺ (future-totalOrder A) (future-totalOrder A) (future-mapTime-Preserves-≤ᵗ, f p) s