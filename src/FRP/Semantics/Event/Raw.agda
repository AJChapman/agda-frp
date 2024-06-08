open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Semantics.Event.Raw
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import FRP.Time Time
open import FRP.Semantics.Event.Type Time renaming (_<$>_ to _<$ᵉ>_)
open import FRP.Semantics.Future Time renaming (_<$>_ to _<$ᶠ>_) using ()

open import Algebra using (RawMonoid)
open import Data.List using ([]; map; [_])
open import Data.Product using (_,_)
open import Effect.Applicative using (RawApplicative)
open import Effect.Functor using (RawFunctor)
open import Effect.Monad using (RawMonad)
open import Relation.Binary.PropositionalEquality using (_≡_)

private
  variable
    A : Set a

event-rawMonoid : Set a → RawMonoid (a ⊔ ℓ) (a ⊔ ℓ)
event-rawMonoid A = record
  { Carrier = Event A
  ; _≈_ = _≡_
  ; _∙_ = merge
  ; ε = empty
  }

event-rawFunctor : RawFunctor Event
event-rawFunctor = record
  { _<$>_ = _<$ᵉ>_ }

-- event-join : Event (Event A) → Event A
-- event-join = ?

-- event-rawApplicative : RawApplicative Event
-- event-rawApplicative = record
--   { rawFunctor = event-rawFunctor
--   ; pure = now
--   ; _<*>_ = {!!} -- {A B : Set a} → Event (A → B) → Event A → Event B
--   -- Would it make sense to:
--   --   1. Drop any As before the first occurence of an A → B,
--   --   2. Apply whichever A → B last occurred to each subsequent A?
--   -- Is this compatible with either of the bind implementations suggested below?
--   -- Apply in terms of bind:
--   --   ef <*> ex = ef >>= (λ f → ex >>= (λ x → pure (f x)))
--   -- If we also make `pure = now`, treating the time as relative, then
--   -- Using bind #2 below:
--   --   Apply (λ f → ex >>= (λ x → pure (f x))) to each A → B event, resulting in:
--   --     Apply (λ x → pure (f x)) to each A event, resulting in:
--   --       An event of Bs occurring at time 0,
--   --     Treat these times as relative to the A event which caused them, resulting in:
--   --       An event of Bs occurring at the same time as the original As
--   --     Join by merging all the resultant event lists
--   --   Treat these times as relative to the A → B event which caused them, resulting in:
--   --     An event of Bs... we would be adding an absolute time to an absolute time :(
--   -- This prompts me to want the meaning of events' times to be relative at all times!
--   }
-- 
-- event-rawMonad : RawMonad Event
-- event-rawMonad = record
--   { rawApplicative = event-rawApplicative
--   ; _>>=_ = λ a f → event-join (f <$ᵉ> a) -- {A B : Set a} → Event A → (A → Event B) → Event B
--   -- Would it make sense to (as per the paper):
--   --   1. Apply the A → Event B to each A, resulting in a Event (Event B)
--   --   2. Delay the occurrences of the Event B to be no earlier than the event which caused it,
--   --   3. Join by merging all the resultant event lists
--   -- Or:
--   --   1. Apply the A → Event B to each A, resulting in a Event (Event B)
--   --   2. Treat the times in each Event B as *relative* to the event which caused it, so add them to the time of that event
--   --   3. Join by merging all the resultant event lists
--   }
-- 