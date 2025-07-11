-- Here is a first `import Mathlib.Tactic` to get things started.
-- Based on the definitions you need, you can add more imports right below.
import Mathlib.Tactic
-- Theoretically, you could just write `import Mathlib`, but this will be somewhat slower.
section continuity
theorem Stetigkeit : ε-δ-Definition der Stetigkeit := by
  -- Sei ε > 0 beliebig.
  intro ε ε_pos,
  -- Da f stetig in l ist, gibt es δ > 0, so dass |x - l| < δ ⇒ |f x - f l| < ε.
  have f_cont_at_l := h_cont l,
  specialize f_cont_at_l ε ε_pos,
  rcases f_cont_at_l with ⟨δ, δ_pos, hδ⟩,
  -- Da (a n) gegen l konvergiert, gibt es N, so dass für n ≥ N gilt: |a n - l| < δ.
  have a_conv := h_lim δ δ_pos,
  rcases a_conv with ⟨N, hN⟩,
  -- Für n ≥ N gilt dann: |f(a n) - f l| < ε.
  use N,
  intros n hn,
  specialize hN n hn,
  apply hδ,
  exact hN,
/- Remember we can open namespaces to shorten names and enable notation.

For example (feel free to change it): -/
open Function Set

/- Remember if many new definitions require a `noncomputable` either in the `section` or definition.

For example (feel free to change it): -/
noncomputable section

/- You can now start writing definitions and theorems. -/
