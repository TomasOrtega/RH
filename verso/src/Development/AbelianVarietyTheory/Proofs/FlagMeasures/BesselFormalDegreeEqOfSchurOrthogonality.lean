import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

/- English proof (translation)
Take `⟨hd, hrel⟩` from `hS`. Take `⟨-, hint⟩` from `hrel w w w w`. Establish `hpt : ∀ g : Mt k r, coef σ w w (Matrix.of g) * star (coef σ w w (Matrix.of g)) = ((‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ)`. Introduce `g`. Simplify using `only [coef]`.

Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Rewrite `hint` using `[hpt]`. Rewrite `hint` using `[integral_complex_ofReal, inner_self_eq_norm_sq_to_K]`. Establish `hreal : ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = ‖w‖ ^ 4 / d`. Apply `Complex.ofReal_injective` to reduce the goal to its premises.

Rewrite using `[hint]`. Use `push_cast`. Rewrite using `[← pow_add]`. Both sides reduce to the same expression. Establish `hn : (0 : ℝ) < ‖w‖` using `norm_pos_iff.mpr hw`.

Unfold `fdegH`. Rewrite using `[hreal]`. Establish `h4 : (‖w‖ ^ 4 : ℝ) ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts.
-/
theorem fdegH_eq_of_schurH (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (d : ℝ) (w : H)
    (hS : SchurH μG σ d) (hw : w ≠ 0) : fdegH μG σ w = d := by
  obtain ⟨hd, hrel⟩ := hS
  obtain ⟨-, hint⟩ := hrel w w w w
  have hpt : ∀ g : Mt k r, coef σ w w (Matrix.of g) * star (coef σ w w (Matrix.of g))
      = ((‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    simp only [coef]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [hpt] at hint
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at hint
  have hreal : ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = ‖w‖ ^ 4 / d := by
    apply Complex.ofReal_injective
    rw [hint]
    push_cast
    rw [← pow_add]
    rfl
  have hn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  unfold fdegH
  rw [hreal]
  have h4 : (‖w‖ ^ 4 : ℝ) ≠ 0 := by positivity
  field_simp

end GlobalTheory.SgInf
