open import Level renaming (_⊔_ to _⊔ₗ_)
open import Data.Unit
open import Data.Bool

module ZeroKnowledge where
open import Relation.Unary
open import Relation.Unary.PredicateTransformer

module ZKP
  {ℓₚ ℓᵥ : Level}
  {a : Set ℓₚ} {b : Set ℓᵥ}
  {α : b → b → Set ℓᵥ}
  where
  open import Relation.Binary

  Verify :  Set ℓᵥ → Set (suc ℓᵥ)
  Verify x = Rel x ℓᵥ

  Prove : Set ℓₚ → Set ℓᵥ → Set _
  Prove p v = PT p v ℓᵥ ℓᵥ

  verify : Verify b
  verify = α

  prove : (b → a) → Prove a b
  prove b∼a p b = p (b∼a b)

open import Relation.Nullary
module ¬¬-zk
  {ℓₚ : Level}
  {a : Set ℓₚ}
  {α : ¬ ¬ a → ¬ ¬ a → Set ℓₚ}
  where
  open import Relation.Nullary.Negation
  open import Data.Empty
  open import Function
  open import Data.Product


  ¬¬ : ∀ {ℓ} {A : Set ℓ}
     → A → ¬ ¬ A
  ¬¬ x ¬x = ¬x x

  f : a → ¬ ¬ a → Bool
  f _ _ = true

  ¬¬α : a → ¬ ¬ a → Bool
  ¬¬α _ _ = true

  open ZKP {ℓₚ} {ℓₚ} {a} {¬ ¬ a} {α}

  ¬¬-verify : Verify (¬ ¬ a)
  ¬¬-verify = verify

  ¬¬-proof : ((¬ ¬ a) → a) → Prove a (¬ ¬ a)
  ¬¬-proof = prove

  ¬¬? : Dec a → Dec (¬ ¬ a)
  ¬¬? = ¬? ∘ ¬?
