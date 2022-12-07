module RepresentationLearning where

-- $ Mine the data for the categorical structure
-- $ Align the categorical structures between datasets
-- $ Discover hierarchical structure with tensor categories

open import Categorical.Raw
open import Functions.Raw
--open import Fun



-- First, we need a Linear Map Category



module Repr
         {o} {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
         {_⇨_ : obj → obj → Set} (let private infix 0 _⇨_; _⇨_ = _⇨_)
         ⦃ _ : Category _⇨_ ⦄ ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : Logic _⇨_ ⦄
  where

  -- infix 0 _⇨ᶻ_
  -- _⇨ᶻ_ : obj → obj → Set
  -- a ⇨ᶻ b = a ⇨ b

  open import Data.Nat
  f : {n : ℕ} → (a : obj) → V a n ⇨ V a n
  f = id
