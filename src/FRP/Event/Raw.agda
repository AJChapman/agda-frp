open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.Event.Raw
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import FRP.T time
open import FRP.Event.Type time

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
  ; ε = []
  }

event-rawFunctor : RawFunctor Event
event-rawFunctor = record
  { _<$>_ = λ f → map λ (t₁ , x) → t₁ , f x }

event-rawApplicative : RawApplicative Event
event-rawApplicative = record
  { rawFunctor = event-rawFunctor
  ; pure = λ x → [ -∞ , x ]
  ; _<*>_ = {!!}
  }

event-rawMonad : RawMonad Event
event-rawMonad = record
  { rawApplicative = event-rawApplicative
  ; _>>=_ = {!!}
  }
