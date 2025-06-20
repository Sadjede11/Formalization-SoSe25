import Mathlib.Tactic
import FormalizationSoSe25.Lectures.Lecture6

section review


/-
Last time we discussed
`structures`, `classes`, `instances`, and `hierarchies`.

For example, we wrote things like:
-/

#print Group₄

instance : Group₄ ℤ where
  dia := Int.add
  one := 0
  inv := Int.neg
  dia_assoc := Int.add_assoc
  one_dia := Int.zero_add
  dia_one := Int.add_zero
  inv_dia := Int.add_left_neg
  dia_inv := Int.add_right_neg

end review

section two_operations
/-
We saw how monoids and groups using `structure` and `class`.
But many mathematical objects have more than one operation.
For example, rings, fields, vector spaces, etc. .
How can we deal with that properly?

The trick is to have *2* separate monoids.
-/

#print Monoid
#print AddMonoid
-- We can define `Ring` as an extension of `Monoid` and `AddMonoid`.
#print Ring

/-
Of course this would mean many results have to be proven twice:
- For addition
- For multiplication

That's not how we should do things.

There is hence a transport mechanism that generates statements
about the additive monoid from the multiplicative monoid.

Here is a simple example:
-/
@[to_additive]
lemma mul_four_assoc₂ {α: Type*} [Semigroup α] (a b c d : α) : (a * b) * (c * d) = a * (b * (c * d)) := by
  simp [Semigroup.mul_assoc]

#check mul_four_assoc₂
#check add_four_assoc₂

@[to_additive]
lemma inv_eq_of_mul {G: Type*} [Group G] {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  calc
    a⁻¹ = a⁻¹ * 1       := by rw [mul_one]
    _   = a⁻¹ * (a * b) := by rw [← h]
    _   = (a⁻¹ * a) * b := by rw [mul_assoc]
    _   = 1 * b         := by rw [inv_mul_cancel a]
    _   = b             := by rw [one_mul]

#check neg_eq_of_add

end two_operations


section morphisms
/-
For given types `X` and `Y`, we can define functions `f : X → Y`, which behave as we expect.
Now, if `X` and `Y` are equipped with some class instance, then `f` should preserve that!

How can we do that? Let us focus on the case of monoids.
-/
#check Monoid
#check MonoidHom

-- A naive approach would be to do a direct definition:
def isMonoidHom₀ {G H : Type*} [Monoid G] [Monoid H] (f : G → H) : Prop :=
  f 1 = 1 ∧ ∀ g g', f (g * g') = f g * f g'

/-
This is clearly the wrong idea, cause the two conditions are combined in a conjunction.
We should have separate fields, similar to `structure` and `class` definitions.
-/

structure isMonoidHom₁ {G H : Type*} [Monoid G] [Monoid H] (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ g g', f (g * g') = f g * f g'

/-
This definition could be reasonable, but is not really how we think about morphisms.
To make things more concrete, here are two example sentences:

1. Let `G`, `H` be two monoids, `f : G → H` a function, such that `f` is a monoid morphism.

2. Let `G`, `H` be two monoids, `f : G → H` a monoid morphism.

Usually, we use the second sentence, so our definition should reflect that.
This means we use the following definition:

Recall that `@[ext]` allows us to use the `ext` tactic to prove two functions are equal.
-/

@[ext]
structure MonoidHom₁ (G H : Type*) [Monoid G] [Monoid H]  where
  toFun : G → H
  map_one : toFun 1 = 1
  map_mul : ∀ g g', toFun (g * g') = toFun g * toFun g'


/-
If we use `isMonoidHom₁` we have to first define a function `f`,
and then make it a homomorphism.
With `MonoidHom₁`, we can do both in one step.
-/
example {G H : Type*} [Monoid G] [Monoid H] (f : G → H) (_ : isMonoidHom₁ f) : f = f :=  by
  rfl

example {G H : Type*} [Monoid G] [Monoid H] (f : MonoidHom₁ G H) : f = f :=  by
  ext -- This line is redundant, but it shows that `ext` works.
  rfl

/-
So `MonoidHom₁` includes a morphisms and the monoid morphism properties.

Of course, we now have to use `toFun` to access the morphism.
-/

variable {G₁ H₁ : Type*} [Monoid G₁] [Monoid H₁] (f : MonoidHom₁ G₁ H₁) {g₁ : G₁}

-- #check f g₁
#check f.toFun g₁

/-
The solution is to include a coercion.
Here we are coercing a function, so we use `CoeFun`.
-/
instance {G H : Type*} [Monoid G] [Monoid H] : CoeFun (MonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := MonoidHom₁.toFun

-- Now we can use `f g₁` instead of `f.toFun g₁`.
#check f g₁

/-
We can use `attribute [coe] MonoidHom₁.toFun` to make the coercion implicit only leaving a  `↑`.
-/
attribute [coe] MonoidHom₁.toFun

#check f g₁

-- We can start stating basic equalities about morphisms.
example {G H : Type*} [Monoid G] [Monoid H] (f : MonoidHom₁ G H) : f 1 = 1 :=  f.map_one

-- We can similarly define the additive version of monoid homomorphisms via `AddMonoidHom₁`.
@[ext]
structure AddMonoidHom₁ (G H : Type*) [AddMonoid G] [AddMonoid H]  where
  toFun : G → H
  map_zero : toFun 0 = 0
  map_add : ∀ g g', toFun (g + g') = toFun g + toFun g'

instance {G H : Type*} [AddMonoid G] [AddMonoid H] : CoeFun (AddMonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := AddMonoidHom₁.toFun

attribute [coe] AddMonoidHom₁.toFun

-- Finally, we can combine these two definitions to define a ring homomorphism.
@[ext]
structure RingHom₁ (R S : Type*) [Ring R] [Ring S] extends MonoidHom₁ R S, AddMonoidHom₁ R S

/-
Here is a problem with this definition.
Our monoid homomorphisms depend on the particular monoid structure we are working with.

Let's say we prove the following basic property of monoid homomorphisms, but using `MonoidHom₁`:
-/

lemma map_inv_of_inv₀ {M N : Type*} [Monoid M] [Monoid N] (f : MonoidHom₁ M N) {m m' : M} (h : m*m' = 1) :
    f m * f m' = 1 := by
  rw [← MonoidHom₁.map_mul, h, MonoidHom₁.map_one]

/-
Then we *cannot* use this lemma for additive monoid homomorphisms or ring homomorphisms.
-/
-- example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : AddMonoidHom₁ M N) {m m' : M} (h : m + m' = 0) :
--     f m + f m' = 0 := map_inv_of_inv₀ f h

-- example {M N : Type*} [Ring M] [Ring N] (f : RingHom M N) {m m' : M} (h : m * m' = 1) :
    -- f m * f m' = 1 := map_inv_of_inv₀ f h

/-
Even more generally, we don't know how to coerce
ring homomorphisms, as there are two options now.

What we need is to abstract away the monoid structure.
We can do this by defining a `class` of monoid homomorphisms.
Then making actual monoid homomorphism `instances` of this class.

Here is a naive definition of a class of monoid homomorphisms.

Here `F` is an arbitrary type, but it should be thought of as
*type of functions from `M` to `N`, which is at least a monoid homomorphism*
-/
class MonoidHomClass₁ (F : Type*) (M N : Type*) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

/-
We saw before how to use `CoeFun` to get a function from `MonoidHom₁`.
We should similarly get a function from `MonoidHomClass₁`.
It should take the data `F`, `M`, and `N` to `.toFun`.

We need that first line to override Lean trying to check the correct order of synthesization
-/

-- set_option synthInstance.checkSynthOrder false in
-- instance {F : Type*} {M N : Type*} [Monoid M] [Monoid N] [MonoidHomClass₁ F M N] : CoeFun F (fun _ ↦ M → N) where
--   coe := MonoidHomClass₁.toFun

-- Here is a simple monoid homomorphism.
def idnat : MonoidHom Nat Nat :=
  { toFun := fun x => x,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl}

-- Already synthesizing this instance will cause problems with our instance above.
set_option trace.Meta.synthInstance true in
#eval idnat 7

/-
In the definition of `MonoidHomClass₁`, we have a problem with the order of synthesization.
We have `F` as a parameter, but `M` and `N` are out parameters, that should really be clear
as soon as we know `F`.

We can fix this by using `outParam` in the definition of `MonoidHomClass₁`.
-/

#check outParam

class MonoidHomClass₂ (F : Type*) (M N : outParam Type*) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

instance {F : Type*} {M N : outParam Type*} [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₂.toFun

attribute [coe] MonoidHomClass₂.toFun

-- We can now check the original example.
#eval idnat 7

/-
We can now use this to define a class of monoid homomorphisms.
-/
instance (M N : Type*) [Monoid M] [Monoid N] : MonoidHomClass₂ (MonoidHom₁ M N) M N where
  toFun := MonoidHom₁.toFun
  map_one := fun f ↦ f.map_one
  map_mul := fun f ↦ f.map_mul

-- But also ring homomorphisms.
instance (R S : Type*) [Ring R] [Ring S] : MonoidHomClass₂ (RingHom₁ R S) R S where
  toFun := fun f ↦ f.toMonoidHom₁.toFun
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul

-- If we prove a lemma once, it applies to all cases.
lemma map_inv_of_inv {M N F : Type*} [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] (f : F) {m m' : M} (h : m*m' = 1) :
    f m * f m' = 1 := by
  rw [← MonoidHomClass₂.map_mul, h, MonoidHomClass₂.map_one]

example {M N : Type*} [Monoid M] [Monoid N] (f : MonoidHom₁ M N) {m m' : M} (h : m*m' = 1) : f m * f m' = 1 :=
map_inv_of_inv f h

example {R S : Type*} [Ring R] [Ring S] (f : RingHom₁ R S) {r r' : R} (h : r*r' = 1) : f r * f r' = 1 :=
map_inv_of_inv f h

/-
At the end we note here that we can abstract one further layer via dependent function types.
This will not be relevant for now.
-/

#check DFunLike
#print DFunLike

class MonoidHomClass₃ (F : Type*) (M N : outParam Type*) [Monoid M] [Monoid N] extends
    DFunLike F M (fun _ ↦ N) where
  map_one : ∀ f : F, f 1 = 1
  map_mul : ∀ (f : F) g g', f (g * g') = f g * f g'

instance (M N : Type*) [Monoid M] [Monoid N] : MonoidHomClass₃ (MonoidHom₁ M N) M N where
  coe := MonoidHom₁.toFun
  coe_injective' _ _ := MonoidHom₁.ext
  map_one := MonoidHom₁.map_one
  map_mul := MonoidHom₁.map_mul

end morphisms

section subobjects
/-
We learned about
- objects (structures, classes)
- morphisms (functions)

So, what's left are *subobjects*!

Recall for a type `X`, we have the type of subobjects
defined as `Set X`, which is by definition `X → Prop`.
-/

#check Set ℕ
/-
We want to refine general subsets to subobjects.

In mathematics we often do this by secretly relating *subsets* and *injections*.
In Lean we can obtain a similar relation via `SetLike`.
-/

#check SetLike
#print SetLike
#print SetLike.mk

#check SetCoe.ext
#print SetCoe.ext

-- Let's see examples.
@[ext]
structure Submonoid₁ (M : Type*) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance {M : Type*} [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' _ _ := Submonoid₁.ext

/-
Here the line `coe_injective'` guarantees that submonoids
are equal if their underlying sets are equal.
-/

-- Because of the coercion, we now have `1 ∈ N` directly.
example {M : Type*} [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

/-
More generally, we can treat N as if it is in `Set M`.
For example we can compute the direct image `f '' N`.
-/
example {M : Type*} [Monoid M] (N : Submonoid₁ M) (α : Type*) (f : M → α) : Set α := f '' N

/-
More generally, writing `x : N` is understood as `x ∈ N`,
i.e. `x : M` and `x` in the subset `N`, as we saw before.
-/
example {M : Type*} [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property

/-
Now using `SetLike` we can define an instance of `Monoid N`
for every submonoid `N` of a monoid `M`.
-/
instance SubMonoid₁Monoid {M : Type*} [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))

/-
An alternative way to define the same instance is to
directly deconstruct the membership of terms in `N`.
-/

instance SubMonoid₁Monoid' {M : Type*} [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)

/-
We now want to generalize to different classes of submonoids.
Similar to `MonoidHomClass₁`, we define it by abstracting by one level.

Here `SubmonoidClass₁` is a type `S` where the terms are at least submonoids of `M`.
-/
class SubmonoidClass₁ (S : Type*) (M : Type*) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance {M : Type*} [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem


/-
We can use the natural lattice structure on `Set M`
to define intersections of submonoids.
-/
instance {M : Type*} [Monoid M] : Min (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

example {M : Type*} [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P

/-
Note this approach only works for intersections, as the union of two
monoids is not a submonoid in general.
This does not mean `N ⊔ P` does not exist, however it needs more effort.
-/

end subobjects
