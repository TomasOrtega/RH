import Formalism.ZetaNonvanishing.RiemannZetaOneNeZeroOfRealMemIoo

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

section Fam

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
  (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ)

/- English proof (authored)
Equality of the embedded real numbers would imply equality of their real parts, which are the original real numbers. This contradicts strict inequality.
-/
lemma ofReal_ne_ofReal_of_lt {a b : ℝ} (h : a < b) : (b : ℂ) ≠ (a : ℂ) := by
  intro h'
  have := congrArg Complex.re h'
  simp at this
  linarith

/- English proof (authored)
If the complex number were the embedding of the real number, its real part would equal that real number, contradicting the strict lower bound.
-/
lemma ne_ofReal_of_lt_re {s : ℂ} {a : ℝ} (h : a < s.re) : s ≠ (a : ℂ) := by
  intro h'
  rw [h'] at h
  simp at h

end Fam

end Formalism
