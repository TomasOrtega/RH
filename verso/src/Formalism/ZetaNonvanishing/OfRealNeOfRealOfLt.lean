import Formalism.ZetaNonvanishing.RiemannZetaOneNeZeroOfRealMemIoo

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

section Fam

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
  (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma ofReal_ne_ofReal_of_lt {a b : ℝ} (h : a < b) : (b : ℂ) ≠ (a : ℂ) := by
  intro h'
  have := congrArg Complex.re h'
  simp at this
  linarith

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.
-/
lemma ne_ofReal_of_lt_re {s : ℂ} {a : ℝ} (h : a < s.re) : s ≠ (a : ℂ) := by
  intro h'
  rw [h'] at h
  simp at h

end Fam

end Formalism
