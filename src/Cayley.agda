{-
To define all the relevant instances for a category of Cayley complexes, we can first define a record that represents a Cayley complex. This can be done as follows:
-}

module Cayley where


module CC where

    open import Level
    --open import Function
    open import Relation.Binary.PropositionalEquality

    open import Categorical.Raw
    open import Categorical.Object

    record CayleyComplex (X : Set) (Y : Set) : Set (suc zero) where
      field
        node : Set → Set
        edge : node X → node X → Set
        square : (x y : node X) → (e₁ e₂ e₃ : edge x y) → Set
        edges-at-node : (x y : node X) → x ≡ y → edge x y
        squares-at-node : (x y : node X) → (e₁ e₂ e₃ : edge x y) → square x y e₁ e₂ e₃ → (e₁ ≡ e₂)
        edge-edge-compose : (x y z : node X) → (e₁ : edge x y) → (e₂ : edge y z) → edge x z
        square-square-compose : (x y z : node X) → (e₁ e₂ e₃ : edge x y) → (e′₁ e′₂ e′₃ : edge y z) → square x y e₁ e₂ e₃ → square y z e′₁ e′₂ e′₃ → square x z (edge-edge-compose x y z e₁ e′₁) (edge-edge-compose x y z e₂ e′₂) (edge-edge-compose x y z e₃ e′₃)


      -- idCC : ∀ (x : node X) → edge x x
      -- idCC = ?
      idCC : (x : node X) → edge x x
      idCC (x) = edges-at-node (x) (x) (refl)
        where open import Function renaming (id to fid)
      _∘CC_ : ∀ (x y z : node X) → edge x y → edge y z → edge x z
      xy ∘CC yz = {!!}


    open CayleyComplex
    instance


      --CCBoolean : Boolean (CayleyComplex)
      --CCBoolean = ?

      CCC : Category (CayleyComplex)
      CCC = record { id = {!!} ; _∘_ = {!!} }




-- record CayleyComplex : Set (suc zero) where
    --   field
    --     node : Set
    --     edge : node → node → Set
    --     square : ∀ {x y z : node} → node → edge x y → edge y z → edge x z → Set
    --     edges-at-node : ∀ {x y : node} → node → edge x y → x ≡ y
    --     squares-at-node : ∀ {x y z w : node} {e₁ : edge x y} {e₂ : edge y x} {e₃ : edge  x} → edge x y → square x e₁ e₂ e₃ → (e₁ ≡ e₂)
    --     edge-edge-compose : ∀ {x y z : node} →  edge x y → edge y z → edge x z
    --     square-square-compose : ∀ {x y : node} {e₁ e₂ e₃ e′₁ e′₂ e′₃}
    --       → square x e₁ e₂ e₃ → square y e′₁ e′₂ e′₃ → square x (edge-edge-compose e₁ e′₁) (edge-edge-compose e₂ e′₂) (edge-edge-compose e₃ e′₃)

    -- CayleyComplexBoolean : Boolean (CayleyComplex)
    -- CayleyComplexBoolean = ?
