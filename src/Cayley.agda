{-
To define all the relevant instances for a category of Cayley complexes, we can first define a record that represents a Cayley complex. This can be done as follows:
-}
open import Categorical.Raw

module Cayley where


record CayleyComplex (obj : Set o) : Set o where
  field
    Carrier : Set
    Carrier = obj
    point : Carrier
    group : Carrier
    add : group -> group -> group
    neg : group -> group
  mul : group -> ℝ -> group
  mul = λ x r -> if r = 0 then point else if r < 0 then neg (mul x (abs r)) else add x (mul x (r - 1))
  smul : ℝ -> group -> group
  smul = λ r x -> if r = 0 then point else if r < 0 then neg (smul (abs r) x) else add (smul (r - 1) x) x
  dist : Carrier -> Carrier -> ℝ
  dist = λ x y -> if x = y then 0 else 1
  conj : Carrier -> Carrier -> Carrier
  conj = λ x y -> if x = y then point else y
  inv : Carrier -> Carrier
  inv = λ x -> if x = point then point else neg x

--$ Next, we can define a Category instance for CayleyComplex, where the morphisms are functions from one Cayley complex to another. This can be done as follows:

instance CayleyComplexCategory (obj₁ obj₂ : CayleyComplex) : Category obj₁ obj₂ where
  field
    id : a -> a
    id = λ x -> x
    ∘ : (b -> c) -> (a -> b) -> (a -> c)
    ∘ = λ f g x -> f (g x)

--$ We can also define instances for Products, Exponentials, and Boolean for CayleyComplex, as follows:

instance CayleyComplexProducts (obj : CayleyComplex) : Products obj where
  field
  ⊤ = point
  × = λ x y -> if x = point then y else if y = point then x else mul x 0.5 (add x y)

instance CayleyComplexExponentials (obj : CayleyComplex) : Exponentials obj where
  field
    ⇛ = λ x y -> if x = point then y else if y = point then x else mul x 0.5 (add x (inv y))

instance CayleyComplexBoolean (obj : CayleyComplex) : Boolean obj where
  field
    Bool = point

-- $ With these instances defined, we can now construct a category of Cayley complexes and use the various operations and properties defined in the records to manipulate and reason about Cayley complexes in a categorical setting.



{-
Faez Shakil
please construct that category

To construct a category of Cayley complexes, we can use the previously defined instances of Category, Products, Exponentials, and Boolean for CayleyComplex. This can be done as follows:
-}


CayleyComplexCategory : Category (CayleyComplex)
CayleyComplexCategory = record
  { obj₁ obj₂ : CayleyComplex
  ⇨ : obj₁ -> obj₂ -> Set ℓ }
  field
    id : a -> a
    id = λ x -> x
    ∘ : (b -> c) -> (a -> b) -> (a -> c)
    ∘ = λ f g x -> f (g x)

CayleyComplexProducts : Products (CayleyComplex)
CayleyComplexProducts = record
  { obj : CayleyComplex }
  field
    ⊤ = point
    × = λ x y -> if x = point then y else if y = point then x else mul x 0.5 (add x y)

CayleyComplexExponentials : Exponentials (CayleyComplex)
CayleyComplexExponentials = record
  { obj : CayleyComplex }
  field
    ⇛ = λ x y -> if x = point then y else if y = point then x else mul x 0.5 (add x (inv y))

CayleyComplexBoolean : Boolean (CayleyComplex)
CayleyComplexBoolean = record
  { obj : CayleyComplex }
  field
  Bool = point


--$ We can then use these instances to construct the category of Cayley complexes as follows:

CayleyComplexCat : Category (CayleyComplex)
CayleyComplexCat =
  { obj : CayleyComplex
  ⇨ : obj -> obj -> Set ℓ }
  record
  field
    id : a -> a
    id = λ x -> x
    ∘ : (b -> c) -> (a -> b) -> (a -> c)
    ∘ = λ f g x -> f (g x)
  × : obj -> obj -> obj
  × = λ x y -> if x = point then y else if y = point then x else mul x 0.5 (add x y)
  ⇛ : obj -> obj -> obj
  ⇛ = λ x y -> if x = point then y else if y = point then x else mul x 0.5 (add x (inv y))
  Bool : obj
  Bool = point

{-
Faez Shakil
Do CayleyComplex instances exist for any of the other records in Categorical.Raw

Yes, we can define CayleyComplex instances for Products, Exponentials, and Boolean using the previously defined constructions for these concepts in the context of Cayley complexes.

For example, the instance for Products can be defined as:
-}


{-
Faez Shakil
What about Cartesian and Traced and Monoid and  IndexedCartesian and CartesianClosed and Logic
-}



We can also define instances for Cartesian, Traced, Monoid, IndexedCartesian, CartesianClosed, and Logic in the context of Cayley complexes.

For example, the instance for Cartesian can be defined as:

CayleyComplexCartesian : Cartesian (CayleyComplex)
CayleyComplexCartesian = record
  { obj : CayleyComplex }
  field
    ! : a -> ⊤
    ! = λ x -> point
    ▵ : (a -> c) -> (a -> d) -> (a -> c × d)
    ▵ = λ f g x -> if x = point then (f point, g point) else mul x 0.5 (add (f x) (g x))
  exl : a × b -> a
  exl = λ x -> fst x
  exr : a × b -> b
  exr = λ x -> snd x
  dup : a -> a × a
  dup = λ x -> (x, x)

Similarly, we can define instances for Traced, Monoid, IndexedCartesian, CartesianClosed, and Logic as follows:

CayleyComplexTraced : Traced (CayleyComplex)
CayleyComplexTraced = record
  { obj : CayleyComplex }
  field
    ∘ₓ : (b -> c) -> (a -> b) -> (a -> c)
    ∘ₓ = λ f g x -> if x = point then f point else f (g x)

CayleyComplexMonoid : Monoid (CayleyComplex)
CayleyComplexMonoid = record
  { obj : CayleyComplex }
  field
    η : a -> 1
    η = λ x -> 1
    μ : (1 -> a) -> a
    μ = λ f -> f 1


CayleyComplexIndexedCartesian : IndexedCartesian (CayleyComplex)
CayleyComplexIndexedCartesian = record
  { obj : CayleyComplex }
  { ℓ }
  { I : Set ℓ }
  field
    Π : (I -> obj) -> obj
    Π = λ f -> point

CayleyComplexCartesianClosed : CartesianClosed (CayleyComplex)
CayleyComplexCartesianClosed = record
  { obj : CayleyComplex }
  field
    ⇀ : (b -> c) -> (a -> b) -> (a -> c)
    ⇀ = λ f g x -> if x = point then f point else f (g x)

CayleyComplexLogic : Logic (CayleyComplex)
CayleyComplexLogic = record
  { obj : CayleyComplex }
  field
    ∧ : a -> a -> a
    ∧ = λ x y -> if x = point then y else if y = point then x else mul x 0.5 (add x y)
    ∨ : a -> a -> a
    ∨ = λ x y -> if x = point then y else if y = point then x else mul x 0.5 (add x (inv y))
    not : a -> a
    not = λ x -> if x = point then point else inv x

-- These instances can be used in further categorical constructions involving Cayley complexes.
