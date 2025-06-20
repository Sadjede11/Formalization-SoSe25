import Mathlib.Tactic
import FormalizationSoSe25.Lectures.Lecture8

section finite_sets

open Finset Fintype
/-
For this exercise recall the following properties of `Finset`:
-/
#check mem_inter
#check mem_union
example (X : Type*) [DecidableEq X] (A B C : Finset X): A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  constructor
  · intro d
    rw [mem_union]
    rw [mem_inter]
    rw [mem_inter]
    rw [mem_inter] at d
    rw [mem_union] at d
    obtain ⟨dP, dQ⟩ := d
    rcases dQ with Q | P
    · left
      constructor
      · exact dP
      · exact Q
    · right
      constructor
      · exact dP
      · exact P

  ·

/-
This next one should be very straightforward, so don't overthink it!
-/
example (X Y : Type*) [Fintype X] [Fintype Y] : card (Fin 2 → (X ⊕ Y)) = (card X)^2 + 2*(card X) * (card Y) + (card Y)^2 := by
  sorry

/-
Recall from the lecture how we can prove the following two properties:
-/
example {X Y : Type*} [DecidableEq X] [ DecidableEq Y] (A B : Finset X) :
  #(A ∪ B) = #A  + #B  -  #(A ∩ B)  := by sorry

example {X Y : Type*} [DecidableEq X] [DecidableEq Y] (A : Finset X) (C : Finset Y) :
  #(A ×ˢ C) = #A * #C := by sorry

/-
Now, use the experience you gained to solve the following exercise.
You might also want to use the following properties of `Nat`:
-/

#check Nat.sub_mul
#check Nat.mul_sub
#check Nat.add_mul
#check Nat.mul_add

example {X Y : Type*} [DecidableEq X] [ DecidableEq Y] (A B : Finset X) (C : Finset Y) :
  #((A ∪ B) ×ˢ C) = #A * #C + #B * #C -  #(A ∩ B) * #C := by
  sorry

end finite_sets

section induction

/-
Here is our new definition of natural numbers.
-/
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

/-
This `namespace` is necessary so we can use `add`, `mul`, ...
without resulting in any conflicts.
-/
namespace MyNat

/-
Inductively complete the following definitions of
`add` and `mul` for `MyNat`.
Your definition should be motivated by what
addition and multiplication of natural numbers should be.
-/
def add : MyNat → MyNat → MyNat
  | x, zero => sorry
  | x, succ y => sorry

/-
Uncomment the following if you have defined `add`.
-/
-- #eval add (succ zero) (succ zero)
/-
It should give us `MyNat.succ (MyNat.succ (MyNat.zero))`
-/

def mul : MyNat → MyNat → MyNat
  | _ , zero => sorry
  | x, succ y => sorry


/-
Uncomment the following if you have defined `mul`.
-/
-- #eval mul (succ (succ zero)) (succ (succ zero))
/-
It should give us `MyNat.succ (MyNat.succ (MyNat.succ (MyNat.succ (MyNat.zero))))`
-/

/-
Now, use the inductive definition to prove the following theorems.
-/
theorem zero_add (n : MyNat) : add zero n = n := by sorry

theorem succ_add (m n : MyNat) : add (succ m) n = succ (add m n) := by sorry

theorem add_comm (m n : MyNat) : add m n = add n m := by sorry

theorem add_assoc (m n k : MyNat) : add (add m n) k = add m (add n k) := by sorry

theorem mul_add (m n k : MyNat) : mul m (add n k) = add (mul m n) (mul m k) := by sorry

theorem zero_mul (n : MyNat) : mul zero n = zero := by sorry

theorem succ_mul (m n : MyNat) : mul (succ m) n = add (mul m n) n := by sorry

theorem mul_comm (m n : MyNat) : mul m n = mul n m := by sorry

end MyNat

end induction

section irrationals
/-
Complete the following proof steps, to show that the square root of `2` is not rational.
-/
example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
    sorry
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 :=
    sorry
  have : 2 ∣ n := by
    sorry
  have : 2 ∣ m.gcd n := by
    sorry
  have : 2 ∣ 1 := by
    sorry
  norm_num at this

/-
If you solve the case for `2` above, you can generalize it to any prime.
You should be able to use a similar approach, however might need the following
additional facts:
-/
#check Nat.Prime.dvd_of_dvd_pow
variable {q : ℕ} (prime_q : q.Prime)
#check prime_q.ne_zero
#check prime_q.ne_one
/-
You might also benefit from the tactic `field_simp` which
can prove `a * b / a = b` with the assumption `a ≠ 0`.
-/

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  sorry

/-
For the next two exercises, you want to use the various facts we established
about the `.factorization` list, we saw in the lecture.
-/

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    sorry
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    sorry
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    sorry
  have eq2 : ((r + 1) * n ^ k).factorization p =
      k * n.factorization p + (r + 1).factorization p := by
    sorry
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  sorry

end irrationals

section infinite_primes
/-
Prove there are infinitely many primes by completing the proof steps.
Here are some things that can help:
-/
#check Nat.dvd_factorial
#check Nat.dvd_sub
/-
Also, if `pp` is a proof that `p` is prime, then `pp.pos` is a proof that `p > 0`.
-/
theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial n + 1 := by
    sorry
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine ⟨p, ?_, pp⟩
  show p > n
  by_contra ple
  push_neg at ple
  have : p ∣ Nat.factorial n := by
    sorry
  have : p ∣ 1 := by
    sorry
  show False
  sorry

end infinite_primes
