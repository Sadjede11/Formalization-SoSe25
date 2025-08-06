-- Here is a first `import Mathlib.Tactic` to get things started.
-- Based on the definitions you need, you can add more imports right below.
import Mathlib.Tactic
-- Theoretically, you could just write `import Mathlib`, but this will be somewhat slower.
import Mathlib.Tactic

section continuity

-- Hier ist eine Lean Definition von Stetigkeit der Abbildung f am Punkt a.
def stetigkeitdef (f: ℝ → ℝ) : Prop :=  ∀ a : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - a| < δ → |f x - f a| < ε

def convergenzdef (a : ℕ → ℝ) (L : ℝ) : Prop := ∀ε > 0, ∃ n0 : ℕ, ∀ n ≥ n0, |(a n) - L| < ε


theorem stetigconvergent (f: ℝ → ℝ) (a : ℕ → ℝ) ( L : ℝ) (fstetig : stetigkeitdef f) ( aLconvergent : convergenzdef a L) : convergenzdef (fun n => f (a n)) (f L) := by
  intro ε εpos
  -- Da f stetig in a ist, gibt es δ > 0, sodass |x - L| < δ ⇒ |f x - f L| < ε
  have hf := fstetig L ε εpos
  obtain ⟨δ, δpos, hδ⟩ := hf
  -- Da a → L, gibt es N, sodass |a n - L| < δ für n ≥ N
  have ha := aLconvergent δ δpos
  obtain ⟨n₁, hN⟩ := ha
  use n₁
  intro n hn
  simp
  apply hδ
  have hNn := hN n hn
  exact hNn
/- Remember we can open namespaces to shorten names and enable notation.

For example (feel free to change it): -/
open Function Set

/- Remember if many new definitions require a `noncomputable` either in the `section` or definition.

For example (feel free to change it): -/
noncomputable section

/- You can now start writing definitions and theorems. -/
