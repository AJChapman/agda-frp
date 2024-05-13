open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.B.Laws
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; module ≡-Reasoning)

open import FRP.B.Type time
open import FRP.B.Raw time public

open import Felix.Laws

module B-laws-instances where instance

  category : Category _→ᵇ_
  category = record
    { identityˡ = λ t _ → refl
    ; identityʳ = λ t _ → refl
    ; assoc     = λ t _ → refl
    ; ∘≈        = λ { {f = f} {k = k} h≈k f≈g t x →
                    trans (h≈k t (f t x)) (cong (k t) (f≈g t x))
                    }
    }
