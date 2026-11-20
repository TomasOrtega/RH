import Formalism.GaussValuationBounds.Statement

namespace Formalism.NOK

/- English proof (translation)
Introduce `g b hg hgb x hx`. Simplify using `only [Finset.mem_union, Finset.mem_Icc] at hx`. Use linear arithmetic over natural numbers and integers.
-/
theorem expNonzero_proof : ExpNonzero := by
  intro g b hg hgb x hx
  simp only [Finset.mem_union, Finset.mem_Icc] at hx
  omega

/- English proof (translation)
Introduce `r s k g e hr hs hg he`. Rewrite using `[max_eq_right (by nlinarith [mul_nonneg hg he])]; ring`.
-/
theorem eTotal_proof : ETotal := by
  intro r s k g e hr hs hg he
  rw [max_eq_right (by nlinarith [mul_nonneg hg he])]; ring

/- English proof (translation)
Introduce `l b b' S E lam hl`. Establish `h1 : l - 1 ≠ 0` using `by linarith`. Establish `h2 : l ≠ 0` using `by linarith`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exponentSumIdentity : ExponentSumIdentity := by
  intro l b b' S E lam hl
  have h1 : l - 1 ≠ 0 := by linarith
  have h2 : l ≠ 0 := by linarith
  field_simp; ring

/- English proof (translation)
Use `⟨fun l hl => ?_, by norm_num⟩` and prove the remaining obligations. Establish `h1 : 0 < l - 1` using `by linarith`. Rewrite using `[div_add_div _ _ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity) (by linarith)]`. Use polynomial arithmetic with `[sq_nonneg (l-13), mul_pos h1 h1, mul_pos (mul_pos h1 h1) h1, sq_nonneg l, mul_pos (mul_pos (mul_pos h1 h1) h1) h1]`.
-/
theorem slopeNum_proof : SlopeNum := by
  refine ⟨fun l hl => ?_, by norm_num⟩
  have h1 : 0 < l - 1 := by linarith
  rw [div_add_div _ _ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity) (by linarith)]
  nlinarith [sq_nonneg (l-13), mul_pos h1 h1, mul_pos (mul_pos h1 h1) h1, sq_nonneg l,
    mul_pos (mul_pos (mul_pos h1 h1) h1) h1]

end Formalism.NOK
