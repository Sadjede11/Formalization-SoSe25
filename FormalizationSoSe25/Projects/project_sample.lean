-- Here is a first `import Mathlib.Tactic` to get things started.
-- Based on the definitions you need, you can add more imports right below.
import Mathlib.Tactic

section continuity

-- Hier ist eine Lean Definition von Stetigkeit der Abbildung f am Punkt a.
def stetigkeitdef (f: ℝ → ℝ) : Prop :=  ∀ a : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - a| < δ → |f x - f a| < ε

def convergenzdef (a : ℕ → ℝ) (L : ℝ) : Prop := ∀ε > 0, ∃ n0 : ℕ, ∀ n ≥ n0, |(a n) - L| < ε


theorem stetigconvergent (f: ℝ → ℝ) (a : ℕ → ℝ) ( L : ℝ) (fstetig : stetigkeitdef f) ( aLconvergent : convergenzdef a L) : convergenzdef (fun n => f (a n) (f L) : by
  intros ε εpos
  -- Da f stetig in a ist, gibt es δ > 0, sodass |x - L| < δ ⇒ |f x - f L| < ε
  have h1 := fstetig L ε εpos
  obtain ⟨δ, δpos, hδ⟩ := exists_prop.mp h1
  -- Da a → L, gibt es N, sodass |a n - L| < δ für n ≥ N
  have h2 := aLconvergent δ δpos
  obtain ⟨N, hN⟩ := exists_prop.mp h2
  use N
  intros n hn
  specialize hN n hn
  specialize hδ (a n) hN
  exact hδ
/- Remember we can open namespaces to shorten names and enable notation.

For example (feel free to change it): -/
open Function Set

/- Remember if many new definitions require a `noncomputable` either in the `section` or definition.

For example (feel free to change it): -/
noncomputable section

/- You can now start writing definitions and theorems. -/
