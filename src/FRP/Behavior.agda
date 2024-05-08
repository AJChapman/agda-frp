module FRP.Behavior
  ( T : Set
  ) where

open import Function using (id; _∘_; const)
open import Relation.Binary.PropositionalEquality using (_≡_; module ≡-Reasoning; cong; refl)

open import FRP.B (T)

-- This is our behavior implementation.
-- For now it's identical to the denotation, but this
-- will change as we develop a more efficient implementation.
Behavior : Set → Set
Behavior A = T → A

-- This maps from the behavior implementation to its denotation.
at : {A : Set} → Behavior A → B A
at = id

time : Behavior T
time = id

-- Functor
fmap : {A B : Set} → (A → B) → Behavior A → Behavior B
fmap f b = f ∘ b

-- `at` is a *natural transformation*, or "functor morphism", from `Behavior` to `B`
at-fmap : ∀ {A B : Set} → (f : A → B) (b : Behavior A) → at (fmap f b) ≡ fmap f (at b)
at-fmap f b =
  begin
    at (fmap f b)
  ≡⟨⟩ -- Definition of `at`
    fmap f b
  ≡⟨ cong (fmap f) refl ⟩
    fmap f (at b)
  ∎ where open ≡-Reasoning

-- Applicative
pure : {A : Set} → A → Behavior A
pure = const

infixl 5 _<*>_
_<*>_ : ∀ {A B : Set} → Behavior (A → B) → Behavior A → Behavior B
f <*> x = λ t → f t (x t)

at-pure : ∀ {A : Set} → (a : Behavior A) → at (pure a) ≡ pure a
at-pure a = refl

at-<*> : ∀ {A B : Set} → (bᶠ : Behavior (A → B)) → (bˣ : Behavior A) → at (bᶠ <*> bˣ) ≡ at bᶠ <*> at bˣ
at-<*> f x = refl
