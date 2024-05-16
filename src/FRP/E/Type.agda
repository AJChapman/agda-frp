open import Level
open import Relation.Binary.Bundles using (DecTotalOrder)

module FRP.E.Type
  {a ℓ : Level}
  (time : DecTotalOrder a ℓ ℓ)
  where

open import Data.List as List using (List)
open import Data.Product using (_×_; _,_)

open import FRP.T time using (T̂; _≤ᵗ?_) public

-- Events occur at certain points in time
𝔼 : Set a → Set a
𝔼 A = List (T̂ × A)

merge : {A : Set a} → 𝔼 A → 𝔼 A → 𝔼 A
merge = List.merge (λ (t₁ , _) (t₂ , _) → t₁ ≤ᵗ? t₂)

mapTimes : {A : Set a} → (T̂ → T̂) → 𝔼 A → 𝔼 A
mapTimes f = List.map (λ (t₁ , x) → (f t₁ , x))
