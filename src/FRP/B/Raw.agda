module FRP.B.Raw
  ( T : Set
  ) where

open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≗_; refl; sym; trans)

open import FRP.B.Type (T)

open import Felix.Raw
open import Felix.Equiv

module B-raw-instances where instance

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
