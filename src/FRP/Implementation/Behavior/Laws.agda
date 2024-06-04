open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Implementation.Behavior.Laws
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import Effect.Applicative as A using (RawApplicative)
open import Effect.Functor as F using (RawFunctor)
open import Relation.Binary.PropositionalEquality using (_≡_; module ≡-Reasoning; cong; refl)

open import FRP.Implementation.Behavior.Type Time
open import FRP.Implementation.Behavior.Raw Time as B using ()
open import FRP.Semantics.Behavior.Raw Time as Bₛ using ()

open import Felix.Laws

-- `at` is a *natural transformation*, or "functor morphism", from `Behavior` to `𝔹`
at-functor-morphism : F.Morphism B.behavior-rawFunctor Bₛ.behavior-rawFunctor
at-functor-morphism = record
  { op = at
  ; op-<$> = λ f x → refl
  }

-- `at` is an applicative morphism from `Behavior` to `𝔹`
at-applicative-morphism : A.Morphism B.behavior-rawApplicative Bₛ.behavior-rawApplicative
at-applicative-morphism = record
  { functorMorphism = at-functor-morphism
  ; op-pure = λ x → refl
  ; op-<*> = λ f x → refl
  }
