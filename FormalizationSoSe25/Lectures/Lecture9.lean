import Mathlib.Tactic

/-
Last time we did a little combinatorics and number theory.

Today we do a little more math, and conretely (linear) algebra.
-/

section groups

/-
Let's see some basic group theory.
-/
#check Group
#print Group

variable (G H: Type*) [Group G] [Group H]

/-
We can also define group homomorphisms.
-/
#check (G →* H)
#check MonoidHom G H

example : (G →* H) = MonoidHom G H := by rfl

#print MonoidHom

/-
There is a tactic for group identities called `group`.
-/
example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

/-
It is already known that subgroups are in fact groups.
-/
example {G : Type*} [Group G] (H : Subgroup G) : Group H := inferInstance

example {G : Type*} [Group G] (H : Subgroup G) : Group {x : G // x ∈ H} := inferInstance

/-
Subgroups can also be normal.
-/

variable (G₀ : Type*) [Group G₀] (H₀ : Subgroup G₀) [H₀.Normal]
#check H₀.Normal


/-
It is already known that quotient groups are in fact groups.
Here we need normal subgroups.
Here the quotient notation is `\/`.
-/
example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance

end groups

section addgroups
/-
There is a version of group theory using addition instead of multiplication.
This is primarily useful when looking at rings later on.
-/
#check AddGroup
#print AddGroup

variable (A B: Type*) [AddGroup A] [AddGroup B]

/-
We can also define group homomorphisms for additive groups.
-/
#check (A →+ B)
#check AddMonoidHom A B

example : (A →+ B) = AddMonoidHom A B := by rfl

#print AddMonoidHom

/-
Additive groups come with a commutative version as well.
-/
#check AddCommGroup
#print AddCommGroup

/-
There is also a tactic for identities in commutative
additive groups called `abel`.
-/

example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel

/-
Note this tactic does *not* work for commutative multiplicative groups.
-/
-- example {G : Type*} [CommGroup G] (x y z : G) : z * x * (y / z / x) = y := by
--   abel

/-
It is already known that additive subgroups are in fact additive groups.
-/
example {G : Type*} [AddGroup G] (H : AddSubgroup G) : AddGroup H := inferInstance

/-
Additive subgroups can also be normal.
-/

variable (A₀ : Type*) [AddGroup A₀] (H₀ : AddSubgroup A₀) [H₀.Normal]
#check H₀.Normal


/-
It is already known that quotient additive groups are in fact additive groups.
-/
example {G : Type*} [AddGroup G] (H : AddSubgroup G) [H.Normal] : AddGroup (G ⧸ H) := inferInstance

end addgroups

section rings
/-
Let us now look at rings.
-/

#check Ring
#print Ring

variable (R S: Type*) [Ring R] [Ring S]

/-
There is a notion of ring homomorphisms.
-/
#check (R →+* S)
#check RingHom R S

example : (R →+* S) = RingHom R S := by rfl

#print RingHom

/-
We already saw a tactic for commutative rings called `ring`.
-/
example {R : Type*} [CommRing R] (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring
/-
But there is also a tactic for non-commutative rings called `noncomm_ring`.
-/
example {R : Type*} [Ring R] (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + x * y  + y * x := by noncomm_ring

/-
Subrings are already known to be rings.
-/
example {R : Type*} [Ring R] (S : Subring R) : Ring S := inferInstance
/-
Besides subrings, we also have ideals.
-/
#check Ideal
#print Ideal
/-
For no particular reason at all, only the quotient of a
commutative ring by an ideal is defined.
-/
-- example {R : Type*} [Ring R] (I : Ideal R) : Ring (R ⧸ I) := inferInstance
example {R : Type*} [CommRing R] (I : Ideal R) : CommRing (R ⧸ I) := inferInstance

end rings

section vectorspaces
/-
Let us now look at vector spaces.

Here we use the word `Module` as it is a special case of a
more general theory.
-/

variable (K : Type*) [Field K]
#check Module K
#print Module

variable (V W: Type*) [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]

/-
We can define linear transformation between vector spaces.
Here the notation is `\to_l`.
-/
#check (V →ₗ[K] W)
#check LinearMap (RingHom.id K)

example : (V →ₗ[K] W) = LinearMap (RingHom.id K) V W := by rfl

#print LinearMap

/-
Sub vector spaces are already known to be vector spaces.
-/
example {V : Type*} [AddCommGroup V] [Module K V] (S : Submodule K V) : Module K S := inferInstance

/-
To each vector space we can associate a dimension.
For technical reasons, in Lean it is called the `rank`.

Unfortunately, finite dimensionality is not completely straightforward.
The dimension of a vector space is defined as the cardinality, rather than just a number.
That way it can incorporate infinite dimensions as well.
-/
#check Module.rank

/-
We can in particular assume a vector space is finite dimensional.
-/
#check FiniteDimensional

end vectorspaces

section matrices
/-
Let us now look at matrices. Lean has its own approach to matrices.
-/

#check Matrix

/-
Again, notice the dimensions of a matrix are *not* numbers, but just types.
If we want finite dimensions, we can use `Fin n` for some natural number `n`.
-/
#check Fin 2

/-
So, now I can define a matrix of size 2x2 over the real numbers as follows:
-/
#check Matrix (Fin 2) (Fin 2) ℝ

/-
How can I define a particular matrix?

There is a vector notation.
-/
#check ![1, 2, 3]

/-
We can generalize this to matrix notation.
-/
#check !![1, 2; 3, 4]
#check !![1, 2; 3, (4:ℤ)]

#check !![1; 2; 3]
#check !![1, 2, 3]

/-
Of course the length of the columns and rows must be consistent.
-/
-- #check !![1,2;3]

/-
We can perform basic operations on matrices and vectors.
-/

-- Addition of vectors
#eval ![1, 2] + ![3, 4]  -- ![4, 6]

-- Addition of matrices
#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]

-- Multiplication matrices
#eval !![1, 2; 3, 4] * !![3, 4; 5, 6]  -- !![13, 16; 29, 36]

/-
Of course for multiplication, the dimensions must be compatible.
-/
#check !![1; 3]
#check !![3, 4; 5, 6]
-- #eval !![1; 3] * !![3, 4; 5, 6]

open Matrix
/-
In the `Matrix` namespace, there are more refined operations.
-/

/-
Vector dot product (or inner product).
Here we use the notation `\cdot_v`.
-/

#eval ![1, 2] ⬝ᵥ ![3, 4]

-- Transpose of a matrix
#eval !![1, 2; 3, 4]ᵀ

-- Determinant of a matrix
#eval !![(1 : ℤ), 2; 3, 4].det
/-
For a determinant, we need:
- A square matrix.
- The entries must be in a commutative ring.
-/

-- #eval !![1,2].det
-- #eval !![1,2; 3, 4].det

-- trace
#eval !![(1 : ℤ), 2; 3, 4].trace
#eval !![1, 2; 3, 4].trace

/-
For the `trace`, we need a square matrix.
-/
-- #eval !![1, 2; 3, 4; 5, 6].trace

/-
Finally, we can compute the inverse of a matrix.
However the approach here will not be very efficient.
-/
#check inv_def
#norm_num [inv_def] !![(1 : ℤ), 2; 3, 4]⁻¹

/-
Here we need to assume the elements of the matrix are in a field.
-/
-- #norm_num [inv_def] !![1, 2; 3, 4]⁻¹

end matrices
