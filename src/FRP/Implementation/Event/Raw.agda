open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Implementation.Event.Raw
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import FRP.Time Time
open import FRP.Implementation.Event.Type Time renaming (_<$>_ to _<$ᵉ>_)

open import Algebra using (RawMonoid)
open import Data.List using ([]; map; [_])
open import Data.Product using (_,_)
open import Effect.Applicative using (RawApplicative)
open import Effect.Functor using (RawFunctor)
open import Effect.Monad using (RawMonad)
open import Relation.Binary.PropositionalEquality using (_≡_)

event-rawMonoid : Set a → RawMonoid a a
event-rawMonoid A = record
  { Carrier = Event A
  ; _≈_ = _≡_
  ; _∙_ = merge
  ; ε = empty
  }

event-rawFunctor : RawFunctor Event
event-rawFunctor = record
  { _<$>_ = _<$ᵉ>_ }

-- event-rawApplicative : RawApplicative Event
-- event-rawApplicative = record
--   { rawFunctor = event-rawFunctor
--   ; pure = λ x → [ -∞ , x ]
--   ; _<*>_ = {!!}
--   }
-- 
-- event-rawMonad : RawMonad Event
-- event-rawMonad = record
--   { rawApplicative = event-rawApplicative
--   ; _>>=_ = {!!}
--   }
-- 