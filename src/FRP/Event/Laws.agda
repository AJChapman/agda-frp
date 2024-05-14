open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.Event.Laws
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import Algebra using (RawMonoid)
open import FRP.Event time using (occs)
import FRP.Event.Raw time as E
import FRP.E.Raw time as 𝔼

open import Algebra.Morphism.Structures using (module MagmaMorphisms; module MonoidMorphisms)
open import Relation.Binary.PropositionalEquality using (refl; cong)

module EventMorphisms (A : Set a) where
    open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)
    open MonoidMorphisms (E.monoid A) (𝔼.monoid A)
    open RawMonoid (E.monoid A) renaming
      ( _≈_ to _≈₁_
      ; _∙_ to _∙₁_
      ; ε to ε₁
      ; rawMagma to rawMagmaE
      )
    open RawMonoid (𝔼.monoid A) renaming
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
