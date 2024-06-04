open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Semantics.Event.Type
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import Data.List as List using (List; [_])
open import Data.Product using (_,_; ∃)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Data.List.Relation.Unary.Sorted.TotalOrder
open import Data.List.Relation.Unary.Sorted.TotalOrder.Properties
open import Data.List.Relation.Unary.Linked as Linked using ([-])

open import FRP.Time Time using (T̂; 0ᵗ; _≤ᵗ_)
open import FRP.Semantics.Future Time
  renaming (_<$>_ to _<$ᶠ>_)
  using (F; mapTime; F-totalOrder; F-decTotalOrder; NotAfter; notAfter?; F-<$>-Preserves-NotAfter; F-mapTime-Preserves-NotAfter)

private
  variable
    A B : Set a

-- Events' occurrences are at points in time relative to a common starting point,
-- and they are sorted by this time (earliest to latest).
-- Negative times are permissible, and may even make sense sometimes!
-- An `Event A` is a list of `F A`s, sorted by time, ascending.
-- Terms of this type are a dependent pair of list and proof that the list is sorted.
Event : Set a → Set (suc a ⊔ ℓ)
Event A = ∃ (Sorted (F-totalOrder A))

-- An event which never occurs
empty : {A : Set a} → Event A
empty = List.[] , Linked.[]

now : A → Event A
now x = [ 0ᵗ , x ] , [-]

-- Merge two events, maintaining their time-sortedness
merge : Event A → Event A → Event A
merge {A} (e₁ , sorted₁) (e₂ , sorted₂) =
  List.merge notAfter? e₁ e₂ , merge⁺ (F-decTotalOrder A) sorted₁ sorted₂

-- Map the given function over each `F A` in the event.
-- You must also provide proof that this mapping preserves the time-sortedness of the event.
map : (f : F A → F B) → (f Preserves (NotAfter {A}) ⟶ (NotAfter {B})) → Event A → Event B
map {A} {B} f p (e , sorted) = List.map f e , map⁺ (F-totalOrder A) (F-totalOrder B) p sorted

-- Map the given function over each `A` in the event
infixl 4 _<$>_
_<$>_ : (A → B) → Event A → Event B
f <$> x = map (f <$ᶠ>_) (F-<$>-Preserves-NotAfter f) x

-- Map the given function over the time of each `F A` in the event.
-- You must also provide proof that this mapping preserves the time-sortedness of the event.
mapTimes : (f : T̂ → T̂) → (f Preserves _≤ᵗ_ ⟶ _≤ᵗ_) → Event A → Event A
mapTimes {A} f p (e , sorted) =
  List.map (mapTime f) e
    , map⁺ (F-totalOrder A) (F-totalOrder A) (F-mapTime-Preserves-NotAfter f p) sorted

