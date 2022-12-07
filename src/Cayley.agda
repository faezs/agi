open import Algebra.Bundles
open import Algebra.Properties.Group
open import Level
open import Relation.Unary
open Algebra.Bundles.Group
open import Data.Sum
--record SymmetricGroup : G where

record Cayley²
  {ℓ ℓ₀}
  (A : Set ℓ)
  (B : Set ℓ₀)
  ⦃ G : Group ℓ ℓ₀ ⦄
  : Set (suc (ℓ ⊔ ℓ₀))
  where
  open Group G renaming (Carrier to X)
  field
    vertices : A ⊎ B
    edges : eᵃ ⊔ eᵇ
