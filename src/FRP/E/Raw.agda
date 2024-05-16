open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.E.Raw
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import FRP.T time
open import FRP.E.Type time

open import Algebra using (RawMonoid)
open import Data.List using ([]; map; [_])
open import Data.Product using (_,_)
open import Effect.Applicative using (RawApplicative)
open import Effect.Functor using (RawFunctor)
open import Effect.Monad using (RawMonad)
open import Relation.Binary.PropositionalEquality using (_≡_)

𝔼-rawMonoid : Set a → RawMonoid a a
𝔼-rawMonoid A = record
  { Carrier = 𝔼 A
  ; _≈_ = _≡_
  ; _∙_ = merge
  ; ε = []
  }

𝔼-rawFunctor : RawFunctor 𝔼
𝔼-rawFunctor = record
  { _<$>_ = λ f → map λ (t₁ , x) → t₁ , f x }

𝔼-rawApplicative : RawApplicative 𝔼
𝔼-rawApplicative = record
  { rawFunctor = 𝔼-rawFunctor
  ; pure = λ x → [ -∞ , x ]
  ; _<*>_ = {!!} -- {A B : Set a} → 𝔼 (A → B) → 𝔼 A → 𝔼 B
  -- Would it make sense to:
  --   1. Drop any As before the first occurence of an A → B,
  --   2. Apply whichever A → B last occurred to each subsequent A?
  -- Is this compatible with either of the bind implementations suggested below?
  -- Apply in terms of bind:
  --   ef <*> ex = ef >>= (λ f → ex >>= (λ x → pure (f x)))
  -- If we also make `pure = λ x → [ 0 , x ]`, treating the time as relative, then
  -- Using bind #2 below:
  --   Apply (λ f → ex >>= (λ x → pure (f x))) to each A → B event, resulting in:
  --     Apply (λ x → pure (f x)) to each A event, resulting in:
  --       An event of Bs occurring at time 0,
  --     Treat these times as relative to the A event which caused them, resulting in:
  --       An event of Bs occurring at the same time as the original As
  --     Join by merging all the resultant event lists
  --   Treat these times as relative to the A → B event which caused them, resulting in:
  --     An event of Bs... we would be adding an absolute time to an absolute time :(
  -- This prompts me to want the meaning of events' times to be relative at all times!
  }

𝔼-rawMonad : RawMonad 𝔼
𝔼-rawMonad = record
  { rawApplicative = 𝔼-rawApplicative
  ; _>>=_ = {!!} -- {A B : Set a} → 𝔼 A → (A → 𝔼 B) → 𝔼 B
  -- Would it make sense to (as per the paper):
  --   1. Apply the A → 𝔼 B to each A, resulting in a 𝔼 (𝔼 B)
  --   2. Delay the occurrences of the 𝔼 B to be no earlier than the event which caused it,
  --   3. Join by merging all the resultant event lists
  -- Or:
  --   1. Apply the A → 𝔼 B to each A, resulting in a 𝔼 (𝔼 B)
  --   2. Treat the times in each 𝔼 B as *relative* to the event which caused it, so add them to the time of that event
  --   3. Join by merging all the resultant event lists
  }
