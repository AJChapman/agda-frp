open import Level
open import FRP.Time.DecOrderedGroup

module FRP.Semantics.Behavior.Laws
  {a ℓ : Level}
  (Time : DecOrderedGroup a ℓ ℓ)
  where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; module ≡-Reasoning)

open import FRP.Semantics.Behavior.Type Time
open import FRP.Semantics.Behavior.Raw Time

open import Felix.Laws

module behavior-laws-instances where instance

  category : Category _→ᵇ_
  category = record
    { identityˡ = λ t _ → refl
    ; identityʳ = λ t _ → refl
    ; assoc     = λ t _ → refl
    ; ∘≈        = λ { {f = f} {k = k} h≈k f≈g t x →
                    trans (h≈k t (f t x)) (cong (k t) (f≈g t x))
                    }
    }
