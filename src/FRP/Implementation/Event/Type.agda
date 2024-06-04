open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Implementation.Event.Type
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import Data.List as List using (List; [_])
open import Data.List.Relation.Unary.Sorted.TotalOrder
open import Data.List.Relation.Unary.Sorted.TotalOrder.Properties
open import Data.List.Relation.Unary.Linked as Linked using ([-])
open import Data.Product using (_,_; ∃)
open import Data.Product using (_×_; _,_)
open import Function using (id)
open import Relation.Binary.Bundles using (DecTotalOrder)
open import Relation.Binary.Core using (_Preserves_⟶_)

open import FRP.Time Time
open import FRP.Semantics.Event Time as S using ()
open import FRP.Semantics.Future Time
  renaming (_<$>_ to _<$ᶠ>_)
  using (F; mapTime; F-totalOrder; F-decTotalOrder; NotAfter; notAfter?; F-<$>-Preserves-NotAfter; F-mapTime-Preserves-NotAfter)

open import Algebra.Construct.NaturalChoice.Max T̂-totalOrder renaming (_⊔_ to _⊔ᵗ_) using (⊔-monoʳ-≤)

private
  variable
    A B : Set a

-- This is our event implementation.
-- For now it's identical to the denotation, but this
-- will change as we develop a more efficient implementation.
Event : Set a → Set (suc a ⊔ ℓ)
Event A = ∃ (Sorted (F-totalOrder A))

-- This maps from the event implementation to its denotation.
occs : Event A → S.Event A
occs = id

-- An event which never occurs
empty : Event A
empty = List.[] , Linked.[]

now : A → Event A
now x = [ 0ᵗ , x ] , [-]

merge : Event A → Event A → Event A
merge {A} (e₁ , sorted₁) (e₂ , sorted₂) =
  List.merge notAfter? e₁ e₂ , merge⁺ (F-decTotalOrder A) sorted₁ sorted₂

delayOccs : (T̂ × Event A) → S.Event A
delayOccs (t̂ₑ , e) = S.mapTimes (t̂ₑ ⊔ᵗ_) (⊔-monoʳ-≤ t̂ₑ) (occs e)

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

