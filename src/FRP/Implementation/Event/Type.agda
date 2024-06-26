open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Implementation.Event.Type
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import Function using (_∘_)
open import Data.List as List using (List; [_])
open import Data.Product using (_×_; _,_)
open import Function using (id)
open import Relation.Binary.Core using (_Preserves_⟶_)

open import FRP.Time Time using (T; 0ₜ; _≤ₜ_; _+ₜ_; T-totalOrder; +-monoʳ-≤ₜ)
open import FRP.Semantics.Event Time as S using ()
open import FRP.Semantics.Future Time
  using (Future; 0ₜ,; mapTime; _<$>ₜ,_; _≤ₜ,_; _≤?ₜ,_; future-<$>-Preserves-≤ₜ,)
open import Algebra.Construct.NaturalChoice.Max T-totalOrder renaming (_⊔_ to _⊔ₜ_) using (⊔-monoʳ-≤)

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
now x = [ 0ₜ, x ]

-- Merge two events, maintaining their time-sortedness
merge : Event A → Event A → Event A
merge {A} e₁ e₂ = List.merge _≤?ₜ,_ e₁ e₂

delayOccs : (T × Event A) → S.Event A
delayOccs (tₑ , e) = S.mapTimes (tₑ ⊔ₜ_) (⊔-monoʳ-≤ tₑ) (occs e)

-- Map the given function over each `Future A` in the event.
-- You must also provide proof that this mapping preserves the time-sortedness of the event.
map : (f : Future A → Future B) → f Preserves _≤ₜ,_ ⟶ _≤ₜ,_ → Event A → Event B
map f _ e = List.map f e

-- Map the given function over each `A` in the event
infixl 4 _<$>_
_<$>_ : (A → B) → Event A → Event B
f <$> x = map (f <$>ₜ,_) (future-<$>-Preserves-≤ₜ, f) x

-- Map the given function over the time of each `Future A` in the event.
-- You must also provide proof that this mapping preserves the time-sortedness of the event.
mapTimes : (f : T → T) → f Preserves _≤ₜ_ ⟶ _≤ₜ_ → Event A → Event A
mapTimes {A} f p e =  List.map (mapTime f) e

addToTimes : T → Event A → Event A
addToTimes t = mapTimes (t +ₜ_) (+-monoʳ-≤ₜ t)

offsetEvents : Event (Event A) → List (Event A)
offsetEvents = List.map (λ (t , e) → addToTimes t e) -- TODO: use mapEvent instead of List.map

joinEvents : Event (Event A) → Event A
joinEvents = List.foldr merge empty ∘ offsetEvents
