open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Implementation.Event.Raw
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import FRP.Time Time
open import FRP.Implementation.Event.Type Time renaming (_<$>_ to _<$>ₑ_)

open import Algebra using (RawMonoid)
open import Data.List using ([]; map; [_])
open import Data.Product using (_,_)
open import Effect.Applicative using (RawApplicative)
open import Effect.Functor using (RawFunctor)
open import Effect.Monad using (RawMonad)
open import Relation.Binary.PropositionalEquality using (_≡_)

private
  variable
    A B : Set a

event-rawMonoid : Set a → RawMonoid a a
event-rawMonoid A = record
  { Carrier = Event A
  ; _≈_ = _≡_
  ; _∙_ = merge
  ; ε = empty
  }

event-rawFunctor : RawFunctor Event
event-rawFunctor = record
  { _<$>_ = _<$>ₑ_ }

pure : A → Event A
pure = now

-- 1. Apply the A → Event B to each A, resulting in an Event (Event B)
-- 2. Treat the times in each Event B as *relative* to the event which caused it, so add them to the time of that event
-- 3. Join by merging all the resultant event lists
infixr 5 _>>=_
_>>=_ : Event A → (A → Event B) → Event B
ea >>= f = joinEvents (f <$>ₑ ea)

infixr 4 _<*>_
_<*>_ : Event (A → B) → Event A → Event B
ef <*> ex = ef >>= (λ f → f <$>ₑ ex)

event-rawApplicative : RawApplicative Event
event-rawApplicative = record
  { rawFunctor = event-rawFunctor
  ; pure = pure
  ; _<*>_ = _<*>_
  }

event-rawMonad : RawMonad Event
event-rawMonad = record
  { rawApplicative = event-rawApplicative
  ; _>>=_ = _>>=_
  }
 