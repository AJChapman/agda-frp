module FRP.Behavior.Laws
  ( T : Set
  ) where

open import Effect.Applicative as A using (RawApplicative)
open import Effect.Functor as F using (RawFunctor)
open import Relation.Binary.PropositionalEquality using (_≡_; module ≡-Reasoning; cong; refl)

open import FRP.Behavior.Type (T)
import FRP.Behavior.Raw (T) as B
import FRP.B.Raw (T) as 𝔹

open import Felix.Laws

-- `at` is a *natural transformation*, or "functor morphism", from `Behavior` to `𝔹`
at-functor-morphism : F.Morphism B.functor 𝔹.functor
at-functor-morphism = record
  { op = at
  ; op-<$> = λ f x → refl
  }

-- `at` is an applicative morphism from `Behavior` to `𝔹`
at-applicative-morphism : A.Morphism B.applicative 𝔹.applicative
at-applicative-morphism = record
  { functorMorphism = at-functor-morphism
  ; op-pure = λ x → refl
  ; op-<*> = λ f x → refl
  }
