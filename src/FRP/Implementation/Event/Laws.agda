open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Implementation.Event.Laws
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import Algebra using (RawMonoid)
open import Algebra.Morphism.Structures using (module MagmaMorphisms; module MonoidMorphisms)
open import Effect.Functor as F using ()
open import Effect.Applicative as A using ()
open import Relation.Binary.PropositionalEquality using (refl; cong)

open import FRP.Implementation.Event.Type Time using (occs)
open import FRP.Implementation.Event.Raw Time as E using ()
open import FRP.Semantics.Event.Raw Time as Eₛ using ()


module EventMorphisms (A : Set a) where
    open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)
    open MonoidMorphisms (E.event-rawMonoid A) (Eₛ.event-rawMonoid A)
    open RawMonoid (E.event-rawMonoid A) renaming
      ( _≈_ to _≈₁_
      ; _∙_ to _∙₁_
      ; ε to ε₁
      ; rawMagma to rawMagmaE
      )
    open RawMonoid (Eₛ.event-rawMonoid A) renaming
      ( _≈_ to _≈₂_
      ; _∙_ to _∙₂_
      ; ε to ε₂
      ; rawMagma to rawMagma𝔼
      )
    open MagmaMorphisms rawMagmaE rawMagma𝔼

    occs-isRelHomomorphism : IsRelHomomorphism _≈₁_ _≈₂_ occs
    occs-isRelHomomorphism = record { cong = cong occs }

    occs-isMagmaHomomorphism : IsMagmaHomomorphism occs
    occs-isMagmaHomomorphism = record
        { isRelHomomorphism = occs-isRelHomomorphism
        ; homo = λ x y → refl
        }

    occs-isMonoidHomomorphism : IsMonoidHomomorphism occs
    occs-isMonoidHomomorphism = record
        { isMagmaHomomorphism = occs-isMagmaHomomorphism
        ; ε-homo = refl
        }

    occs-functorMorphism : F.Morphism E.event-rawFunctor Eₛ.event-rawFunctor
    occs-functorMorphism = record
      { op = occs
      ; op-<$> = λ f x → refl
      }

--     occs-applicativeMorphism : A.Morphism E.event-rawApplicative Eₛ-event-rawApplicative
--     occs-applicativeMorphism = record
--       { functorMorphism = occs-functorMorphism
--       ; op-pure = λ x → refl
--       ; op-<*> = λ f x → refl
--       }
-- 
--     occs-monadMorphism : M.Morphism E.event-rawMonad Eₛ-event-rawMonad
--     occs-monadMorphism = record
--       {
--       }
