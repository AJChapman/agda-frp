open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Semantics.Event.Type
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import Data.List as List using (List; [_])
open import Data.Product using (_,_)
open import Relation.Binary.Core using (_Preserves_⟶_)

open import FRP.Time Time using (T̂; 0ᵗ; _≤ᵗ_)
open import FRP.Semantics.Future Time
  renaming (_<$>_ to _<$ᶠ>_)
  using (Future; mapTime; _≤ᵗ,_; _≤?ᵗ,_; future-<$>-Preserves-≤ᵗ,)

private
  variable
    A B : Set a

-- Events' occurrences are at points in time relative to a common starting point,
-- and they are sorted by this time (earliest to latest).
-- Negative times are permissible, and may even make sense sometimes!
-- An `Event A` is a list of `Future A`s, sorted by time, ascending.
Event : Set a → Set a
Event A = List (Future A)

-- An event which never occurs
empty : Event A
empty = List.[]

now : A → Event A
now x = [ 0ᵗ , x ]

-- Merge two events, maintaining their time-sortedness
merge : Event A → Event A → Event A
merge {A} e₁ e₂ = List.merge _≤?ᵗ,_ e₁ e₂

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

