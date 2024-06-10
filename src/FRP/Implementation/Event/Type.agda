open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Implementation.Event.Type
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import Data.List as List using (List; [_])
open import Data.Product using (_×_; _,_)
open import Function using (id)
open import Relation.Binary.Core using (_Preserves_⟶_)

open import FRP.Time Time using (T̂; 0ᵗ; _≤ᵗ_; T̂-totalOrder)
open import FRP.Semantics.Event Time as S using ()
open import FRP.Semantics.Future Time
  renaming (_<$>_ to _<$ᶠ>_)
  using (Future; mapTime; _≤ᵗ,_; _≤?ᵗ,_; future-<$>-Preserves-≤ᵗ,)
open import Algebra.Construct.NaturalChoice.Max T̂-totalOrder renaming (_⊔_ to _⊔ᵗ_) using (⊔-monoʳ-≤)

private
  variable
    A B : Set a

-- This is our event implementation.
-- For now it's identical to the denotation, but this
-- will change as we develop a more efficient implementation.
Event : Set a → Set a
Event A = List (Future A)

-- This maps from the event implementation to its denotation.
occs : Event A → S.Event A
occs = id

-- An event which never occurs
empty : Event A
empty = List.[]

now : A → Event A
now x = [ 0ᵗ , x ]

-- Merge two events, maintaining their time-sortedness
merge : Event A → Event A → Event A
merge {A} e₁ e₂ = List.merge _≤?ᵗ,_ e₁ e₂

delayOccs : (T̂ × Event A) → S.Event A
delayOccs (t̂ₑ , e) = S.mapTimes (t̂ₑ ⊔ᵗ_) (⊔-monoʳ-≤ t̂ₑ) (occs e)

-- Map the given function over each `Future A` in the event.
-- You must also provide proof that this mapping preserves the time-sortedness of the event.
map : (f : Future A → Future B) → f Preserves _≤ᵗ,_ ⟶ _≤ᵗ,_ → Event A → Event B
map f _ e = List.map f e

-- Map the given function over each `A` in the event
infixl 4 _<$>_
_<$>_ : (A → B) → Event A → Event B
f <$> x = map (f <$ᶠ>_) (future-<$>-Preserves-≤ᵗ, f) x

-- Map the given function over the time of each `Future A` in the event.
-- You must also provide proof that this mapping preserves the time-sortedness of the event.
mapTimes : (f : T̂ → T̂) → f Preserves _≤ᵗ_ ⟶ _≤ᵗ_ → Event A → Event A
mapTimes {A} f p e =  List.map (mapTime f) e

