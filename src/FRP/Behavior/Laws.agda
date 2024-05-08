module FRP.Behavior.Laws
  ( T : Set
  ) where

open import Relation.Binary.PropositionalEquality using (_≡_; module ≡-Reasoning; cong; refl)

open import FRP.Behavior.Type (T)
open import FRP.Behavior.Raw (T) public

open import Felix.Laws

module Behavior-laws-instances where instance
  -- TODO: use MakeLawful after defining homomorphisms to 𝔹

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

at-pure : ∀ {A : Set} → (a : Behavior A) → at (pure a) ≡ pure a
at-pure a = refl

at-<*> : ∀ {A B : Set} → (bᶠ : Behavior (A → B)) → (bˣ : Behavior A) → at (bᶠ <*> bˣ) ≡ at bᶠ <*> at bˣ
at-<*> f x = refl
