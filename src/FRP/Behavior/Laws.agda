open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.Behavior.Laws
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import Effect.Applicative as A using (RawApplicative)
open import Effect.Functor as F using (RawFunctor)
open import Relation.Binary.PropositionalEquality using (_≡_; module ≡-Reasoning; cong; refl)

open import FRP.Behavior.Type time
open import FRP.Behavior.Raw time using (behavior-rawFunctor; behavior-rawApplicative)
open import FRP.B.Raw time using (𝔹-rawFunctor; 𝔹-rawApplicative)

open import Felix.Laws

-- `at` is a *natural transformation*, or "functor morphism", from `Behavior` to `𝔹`
at-functor-morphism : F.Morphism behavior-rawFunctor 𝔹-rawFunctor
at-functor-morphism = record
  { op = at
  ; op-<$> = λ f x → refl
  }

-- `at` is an applicative morphism from `Behavior` to `𝔹`
at-applicative-morphism : A.Morphism behavior-rawApplicative 𝔹-rawApplicative
at-applicative-morphism = record
  { functorMorphism = at-functor-morphism
  ; op-pure = λ x → refl
  ; op-<*> = λ f x → refl
  }
