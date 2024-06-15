open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Semantics.Event.Type
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import Function using (_∘_)
open import Data.List as List using (List; [_])
open import Data.Product using (_,_)
open import Relation.Binary.Core using (_Preserves_⟶_)

open import FRP.Time Time using (T; _≤ₜ_; _+ₜ_;  +-monoʳ-≤ₜ)
open import FRP.Semantics.Future Time using (mapTime; 0ₜ,; _<$>ₜ,_; Future; _≤ₜ,_; _≤?ₜ,_; future-<$>-Preserves-≤ₜ,)

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
now x = [ 0ₜ, x ]

-- Merge two events, maintaining their time-sortedness
merge : Event A → Event A → Event A
merge e₁ e₂ = List.merge _≤?ₜ,_ e₁ e₂

-- Map the given function over each `Future A` in the event.
-- You must also provide proof that this mapping preserves the time-sortedness of the event.
mapEvent : (f : Future A → Future B) → f Preserves _≤ₜ,_ ⟶ _≤ₜ,_ → Event A → Event B
mapEvent f _ e = List.map f e

-- Map the given function over each `A` in the event
infixl 4 _<$>_
_<$>_ : (A → B) → Event A → Event B
f <$> x = mapEvent (f <$>ₜ,_) (future-<$>-Preserves-≤ₜ, f) x

-- Map the given function over the time of each `Future A` in the event.
-- You must also provide proof that this mapping preserves the time-sortedness of the event.
mapTimes : (f : T → T) → f Preserves _≤ₜ_ ⟶ _≤ₜ_ → Event A → Event A
mapTimes f p e = List.map (mapTime f) e

addToTimes : T → Event A → Event A
addToTimes t = mapTimes (t +ₜ_) (+-monoʳ-≤ₜ t)

offsetEvents : Event (Event A) → List (Event A)
offsetEvents = List.map (λ (t , e) → addToTimes t e) -- TODO: use mapEvent instead of List.map

joinEvents : Event (Event A) → Event A
joinEvents = List.foldr merge empty ∘ offsetEvents
