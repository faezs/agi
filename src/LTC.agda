
--open import Categorical.Raw
--open import Functions.Raw
open import Function

--record InverseSemigroup : Set where
open import Algebra.Bundles
module LTC
         {o} {obj : Set o} -- ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
         ⦃ r : Ring o o ⦄
         {_⇨_ : obj → obj → Set} (let private infix 0 _⇨_; _⇨_ = _⇨_)
         -- ⦃ _ : Category _⇨_ ⦄ ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : Logic _⇨_ ⦄
  where

private variable a b c : obj
open import Data.Nat

infix 0 _⇨ᶻ_
_⇨ᶻ_ : obj → obj → Set
a ⇨ᶻ b = a ⇨ b



--ltc : ∀ (k q : ℕ)

module Δ where
  open Algebra.Bundles.Ring r renaming (Carrier to R)
  open import Data.Nat
  open import Data.Vec.Functional
  open import Data.Bool


  B = Data.Bool.Bool

  𝔽ⁿ₂ : ℕ → Set
  𝔽ⁿ₂ n = Vector B n

  un𝔽ⁿ₂ : ∀ (n : ℕ) → 𝔽ⁿ₂ n → Vector B n
  un𝔽ⁿ₂ = λ n x x₁ → x x₁

  --$ This definition makes rate always comes out as 1
  --$ in actuality it should depend on what proportion of 𝔽ⁿ₂ n
  --$ is information-theoretically relevant for us.
  dim : ∀ {n : ℕ} → 𝔽ⁿ₂ n → ℕ
  dim {n} _ = n

  open import Data.Nat.DivMod using (_/_)
  rate : (n : ℕ) → 𝔽ⁿ₂ n → ℕ
  rate ℕ.zero _ = 0
  rate (suc n) c = dim c / suc n

  _δ_ : B → B → ℕ
  Bool.false δ Bool.false = 1
  Bool.false δ Bool.true = 0
  Bool.true δ Bool.false = 0
  Bool.true δ Bool.true = 1


  hamming : ∀ (n : ℕ) → 𝔽ⁿ₂ n → 𝔽ⁿ₂ n → ℕ
  hamming (n) a = sum' ∘ l a
    where
      l : 𝔽ⁿ₂ n → 𝔽ⁿ₂ n → Vector ℕ n
      l = zipWith _δ_
      sum' : Vector ℕ n → ℕ
      sum' a = foldl Data.Nat._+_ 0 a
open Δ public -- {{...}}

module CayleyGraph {V : Set} {n : ℕ} {E : V -> V -> B} where
  -- Import the Data.Nat and Data.Vec modules
  open import Data.Nat
  open import Data.Vec
  open import Data.Vec.Functional
  open import Data.Fin
  open import Data.Product


  -- Define the type of Cayley graphs
  data CayleyGraph V E : Set where
    cayleyGraph : (vertices : Vec V (suc n))
      -> (adjacency : Vec (Fin (suc n)) (suc n))
      -> CayleyGraph V E

  -- Define a function that constructs a Cayley graph for a given set of vertices and edge relation
  cayleyGraph' : ∀ (n : ℕ) → Vec V (suc n) -> CayleyGraph V E
  cayleyGraph' vertices = cayleyGraph vertices adj
    where
      -- Define the adjacency matrix for the graph
      adj : Vec (Fin (suc n)) (suc n)
      adj = Data.Vec.map f vertices
        where
          f : V → ℕ → (Fin n) × n
          f i j = {! E (lookup vertices i) (index vertices j))!}


module SmooothMan {n : ℕ} where

  -- Import the Data.Fin, Data.Vec, and Data.Tree modules
  open import Data.Fin
  open import Data.Vec
  open import Data.Tree.Binary
  open import Data.Product

  -- -- Define a type alias for the point type
  -- Point : Set
  -- Point = Fin (suc n)

  -- -- Define a type alias for the coordinate function type
  -- CoordinateFunction : Set
  -- CoordinateFunction = Fin (suc n) -> Fin (suc n) -> (Fin (suc n) -> Fin (suc n))

  -- -- Define the type of smooth manifolds
  -- data SmoothManifold : (n : ℕ) -> Set where
  --   smoothManifold' : (points : Tree Point) -> (coordinates : CoordinateFunction) -> SmoothManifold n

  -- private variable
  --   coordinates : CoordinateFunction

  -- open import Relation.Unary
  -- open import Data.Bool

  -- smooth : (A : Set) (B : Set) -> (f : A -> B) -> Bool
  -- smooth A B f =
  --   -- Check if the function is infinitely differentiable
  --   all (\n -> isDifferentiable f n) (finNat (suc ∞))


  -- -- Define the laws of a smooth manifold
  -- data SmoothManifoldLaws (n : ℕ) (manifold : SmoothManifold n) (coordinates : CoordinateFunction) : Set where
  --   -- Add the smoothness law for the coordinate functions
  --   Smoothness : ∀ (i j : Fin (suc n)) -> (coordinates i j) ∈ smooth

  --   -- Add the differentiability law for the coordinate functions
  --   Differentiability : ∀ (i j : Fin (suc n)) -> coordinates i j ∈ differentiable

  --   -- Add the Hausdorffness, second-countability, and locally Euclideanness laws for the smooth manifold
  --   Hausdorffness : ∀ a b -> a ≢ b -> ∃ x y -> (x ∈ (open' a)) ∧ (y ∈ (open' b)) ∧ (x ∩ y) ≡ ∅
  --   SecondCountability : ∃ bs -> bs ∈ countable ∧ ∀ u -> u ∈ open' → ∃ v -> v ∈ bs ∧ v ⊆ u
  --   LocallyEuclidean : ∀ p -> ∃ q -> q ∈ open' p ∧ q ≅ open' euclidean

  -- -- Define a function that constructs a smooth manifold with a given set of points and coordinate functions
  -- smoothManifold : (n : ℕ) -> Tree Point -> CoordinateFunction -> SmoothManifold n
  -- smoothManifold = smoothManifold'


--   -- Define the Category type, which represents a category
-- record Category : Set where
--   -- Define the data constructors for the category
--   point : Set -> Category
--   hom : (A B : Category) -> Set
--   id : Category -> hom A A
--   _∘_ : (A B C : Category) -> hom B C -> hom A B -> hom A C

--   -- Define the left identity law for the category
--   leftIdentityLaw : (A B : Category) -> (f : hom A B) -> id B ∘ f ≡ f
--   leftIdentityLaw A B f = refl

--   -- Define the right identity law for the category
--   rightIdentityLaw : (A B : Category) -> (f : hom A B) -> f ∘ id A ≡ f
--   rightIdentityLaw A B f = refl

--   -- Define the associativity law for the category
--   associativityLaw : (A B C D : Category) -> (f : hom C D) -> (g : hom B C) -> (h : hom A B) -> (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
--   associativityLaw A B C D f g h = refl


-- -- Define the SmoothManifold type, which represents a smooth manifold
-- record SmoothManifold : Set where
--   -- Define the data constructors for the smooth manifold
--   point : Set -> SmoothManifold
--   chart : (A : SmoothManifold) -> (U : Set) -> (φ : U -> point A) -> SmoothManifold

--   -- Define the Category instance for the smooth manifold
--   instance Category SmoothManifold where
--     -- Define the hom function for the smooth manifold
--     hom A B = (f : A -> B) -> (p : f ∘ id A ≡ f) -> Set

--     -- Define the identity morphism for the smooth manifold
--     id A f p = f

--     -- Define the composition function for the smooth manifold
--     f ∘ g = g ∘ f

--     -- Define the pointwise equality law for the smooth manifold
--     pointwiseEqualityLaw : (A B : SmoothManifold) -> (f g : hom A B) -> (p : f ∘ id A ≡ f) -> (q : g ∘ id A ≡ g) -> f ≡ g -> f ∘ id A ≡ g ∘ id A
--     pointwiseEqualityLaw A B f g p q eq = eq

--     -- Define the pointwise inequality law for the smooth manifold
--     pointwiseInequalityLaw : (A B : SmoothManifold) -> (f g : hom A B) -> (p : f ∘ id A ≡ f) -> (q : g ∘ id A ≡ g) -> f ≢ g -> f ∘ id A ≢ g ∘ id A
--     pointwiseInequalityLaw A B f g p q eq = eq

--     -- -- Define the pointwise non-degeneracy law for the smooth manifold
--     -- pointwiseNonDegeneracyLaw : (A B : SmoothManifold) -> (f : hom A B) -> (p : f ∘ id A ≡ f) -> ¬ f ≡ id B
--     -- pointwiseNon


open import Relation.Unary
open import Data.Product
open import Algebra.Bundles


record SmoothManifold {{b : BooleanAlgebra}} : Set where
  open BooleanAlgebra b
  -- Define the data constructors for the smooth manifold
  point : Set -> SmoothManifold
  chart : (A : SmoothManifold) -> (U : Set) -> (φ : U -> point A) -> SmoothManifold

  openSubset : {A : SmoothManifold} -> (U : Set) -> Set
  openSubset A U = ∀ (V : Set) x (φ : V -> point A) -> x ∈ U -> ∃ V (φ) -> V ⊆ U ∧ chart A V φ


  -- Define the open subset condition for the smooth manifold
  openSubsetCondition : (A : SmoothManifold) -> A ∈ openSubset A
  openSubsetCondition A = refl

  -- Define the Hausdorff condition for the smooth manifold
  Hausdorffness : (A : SmoothManifold) -> A is Hausdorff
  Hausdorffness A = refl

  -- Define the second countability condition for the smooth manifold
  SecondCountability : ∃ bs -> bs ∈ countable ∧ ∀ a -> a ∈ openSubset a ∧ ∃ b -> b ∈ bs ∧ b ⊆ a
  SecondCountability = refl

  -- Define the continuity condition for the smooth manifold
  Continuity : (A B : SmoothManifold) -> (f : hom A B) -> f is continuous
  Continuity A B f = refl

  -- Define the differentiability condition for the smooth manifold
  Differentiability : (A B : SmoothManifold) -> (f : hom A B) -> f is differentiable
  Differentiability A B f = refl

  -- Define the smooth manifold morphism type
  data ~> : SmoothManifold -> SmoothManifold -> Set where
    -- Define the morphism constructor
    morphism : (A B : SmoothManifold) -> (f : hom A B) -> (A ~> B)

  -- Define the Category instance for the smooth manifold
  instance Category SmoothManifold where
    -- Define the identity morphism
    identity : (A : SmoothManifold) -> A ~> A
    identity A = morphism A A (hom-refl A)

    -- Define the composition of morphisms
    compose : (A B C : SmoothManifold) -> (f : A ~> B) -> (g : B ~> C) -> (A ~> C)
    compose A B C (morphism A B f) (morphism B C g) = morphism A C (hom-trans f g)

    -- Define the proof of composition for smooth manifolds
    proof : (A B C : SmoothManifold) -> (f : A ~> B) -> (g : B ~> C) -> ((compose f g) ≡ (morphism A C (hom-trans (toMorphism f) (toMorphism g))))
    proof A B C f g = refl
