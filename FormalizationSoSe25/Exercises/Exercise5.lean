import Mathlib.Tactic

section triple_constructors

-- Recall the integers are defined as `\bZ`.
#check ℤ

/-
Use `structure` to construct a new constructor:
* It is called `new_triple`
* The data should be three integers `x` `y` `z` in `ℤ`
* It should satisfy `extensionality`
-/

@[ext]
structure new_triple where
   x : ℤ
   y : ℤ
   z : ℤ



/-
Now, solve the following exercises about `new_triple`:

1. Create three instances of `new_triple` using three different approaches:
   * With `.mk`
   * With `⟨⟩`
   * With `where`
   using the numbers `x = 1`, `y = 2`, `z = -3`.
-/

example : new_triple := new_triple.mk 1 2 (-3)

example : new_triple where
  x := 1
  y := 2
  z := -3



/-
2. Uncomment the following line and prove it.
-/

example (x₁ y₁ z₁ x₂ y₂ z₂ : ℤ) : (x₁ = x₂) ∧ (y₁ = y₂) ∧ (z₁ = z₂) ↔ (⟨x₁, y₁, z₁⟩ : new_triple )= (⟨x₂, y₂, z₂⟩ : new_triple) := by
constructor
· rintro  ⟨eqx, eqy, eqz⟩
  ext
  · exact eqx
  · exact eqy
  · exact eqz
· intro h
  cases h




/-
3. Define a namespace `new_triple` and define the following functions:
    * `add` that adds two `new_triple` objects.
    * `mul` that multiplies two `new_triple` objects.
    * `sub` that subtracts two `new_triple` objects.
  Close the namespace `new_triple`.
-/

/-
4. Use `#eval` to compute
    * addition of `⟨1, 2, -3⟩` and `⟨2, -5, 6⟩)`
    * multiplication of `(⟨2, -3, 2⟩` and `⟨1, -2, 2⟩`
    * subtraction of `⟨-1, 2, -3⟩` and `⟨4, 1, 3⟩)`
   For this you want to use `#eval` to evaluate an expression.
-/

/-
5. Reopen the namespace `new_triple` and prove:
   * `mul` is commutative by defining and proving `mul_comm`.
   * `mul` is associative by defining and proving `mul_assoc`.
   Close the namespace `new_triple`.
-/

/-
6. Use `#check` to compare the definition of `new_triple.mul_comm` and `mul_comm`.
-/


end triple_constructors
