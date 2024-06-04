open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Semantics.Behavior.Raw
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import Function using (const; _∘_)
open import Effect.Applicative using (RawApplicative)
open import Effect.Functor using (RawFunctor)
open import Relation.Binary.PropositionalEquality using (_≗_; refl; sym; trans)

open import FRP.Semantics.Behavior.Type Time

open import Felix.Raw using (Category)
open import Felix.Equiv using (Equivalent)

behavior-rawFunctor : RawFunctor Behavior
behavior-rawFunctor = record { _<$>_ = λ f b → f ∘ b }

behavior-rawApplicative : RawApplicative Behavior
behavior-rawApplicative = record
  { rawFunctor = behavior-rawFunctor
  ; pure = const
  ; _<*>_ = λ f x t → f t (x t)
  }

module behavior-raw-instances where instance

  category : Category _→ᵇ_
  category = record { id = idᵇ; _∘_ = _∘ᵇ_ }

  equivalent : Equivalent _ _→ᵇ_
  equivalent = record
    { _≈_ = λ f g → (∀ t → f t ≗ g t)
    ; equiv = record
      { refl = λ _ _ → refl
      ; sym = λ f~g t x → sym (f~g t x)
      ; trans = λ f~g g~h t x → trans (f~g t x) (g~h t x)
      }
    }
