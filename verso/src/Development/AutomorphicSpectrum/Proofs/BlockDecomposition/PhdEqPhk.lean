import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.BigCell

variable {F : Type} [Field F]

open Classical in

/- English proof (translation)
Establish `hd : (!![(r 1)⁻¹, 0; r 0, r 1] : Matrix (Fin 2) (Fin 2) F).det ≠ 0`. Simplify using `[Matrix.det_fin_two, hv]`. Unfold `hr`. Rewrite using `[dif_pos hd]`. Both sides reduce to the same expression.
-/
theorem hr_val (r : Fin 2 → F) (hv : r 1 ≠ 0) :
    (hr r).val = !![(r 1)⁻¹, 0; r 0, r 1] := by
  have hd : (!![(r 1)⁻¹, 0; r 0, r 1] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    simp [Matrix.det_fin_two, hv]
  unfold hr
  rw [dif_pos hd]
  rfl

/- English proof (translation)
Establish `hy : (y : F) ≠ 0` using `y.ne_zero`. Simplify using `only [Units.val_mul, hr_val r hv]`. Simplify using `only [dg2, w0, uni2]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`.

Apply the tactic sequence `simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring`.
-/
theorem cell_val (y : Fˣ) (t : F) (r : Fin 2 → F) (hv : r 1 ≠ 0) :
    (dg2 y 1 * w0 * uni2 t * hr r : GL (Fin 2) F).val =
      !![(y : F) * r 0, (y : F) * r 1; -(r 1)⁻¹ - t * r 0, -(t * r 1)] := by
  have hy : (y : F) ≠ 0 := y.ne_zero
  simp only [Units.val_mul, hr_val r hv]
  simp only [dg2, w0, uni2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/- English proof (translation)
Rewrite using `[cell_val y t r hv, Matrix.det_fin_two_of]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cell_det (y : Fˣ) (t : F) (r : Fin 2 → F) (hv : r 1 ≠ 0) :
    ((dg2 y 1 * w0 * uni2 t * hr r : GL (Fin 2) F).val).det = y := by
  rw [cell_val y t r hv, Matrix.det_fin_two_of]
  field_simp
  ring

end GlobalTheory.CompanionTheory.BigCell

namespace GlobalTheory.CompanionTheory.BigCell

/- English proof (translation)
Introduce `F _ _ _ _ _ _ ψ _ Φ y t r₂ hv`. Establish `hy : (y : F) ≠ 0` using `y.ne_zero`. Unfold `phd phk`. Use `MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)` and prove the remaining obligations. Establish `hrow : (fun j => (dg2 y 1 * w0 * uni2 t * hr r₂ : GL (Fin 2) F).val 0 j / ((dg2 y 1 * w0 * uni2 t * hr r₂ : GL (Fin 2) F).val).det) = r₂`.

Use function extensionality and compare the values at `j`. Rewrite using `[cell_det y t r₂ hv, cell_val y t r₂ hv]`. Apply the tactic sequence `fin_cases j <;> simp`. Establish `hph : r 0 * (dg2 y 1 * w0 * uni2 t * hr r₂ : GL (Fin 2) F).val 1 1 - r 1 * (dg2 y 1 * w0 * uni2 t * hr r₂ : GL (Fin 2) F).val 1 0 = r 1 / r₂ 1 - t * (r 0 * r₂ 1 - r 1 * r₂ 0)`. Rewrite using `[cell_val y t r₂ hv]`.

Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `only []`. Rewrite using `[hrow, hph]`.
-/
theorem phd_eq_phk : Ad3.K.GL2LocalData.GodementKernelBigCell := by
  intro F _ _ _ _ _ _ ψ _ Φ y t r₂ hv
  have hy : (y : F) ≠ 0 := y.ne_zero
  unfold phd phk
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  have hrow : (fun j => (dg2 y 1 * w0 * uni2 t * hr r₂ : GL (Fin 2) F).val 0 j /
      ((dg2 y 1 * w0 * uni2 t * hr r₂ : GL (Fin 2) F).val).det) = r₂ := by
    funext j
    rw [cell_det y t r₂ hv, cell_val y t r₂ hv]
    fin_cases j <;> simp
  have hph : r 0 * (dg2 y 1 * w0 * uni2 t * hr r₂ : GL (Fin 2) F).val 1 1 -
      r 1 * (dg2 y 1 * w0 * uni2 t * hr r₂ : GL (Fin 2) F).val 1 0 =
      r 1 / r₂ 1 - t * (r 0 * r₂ 1 - r 1 * r₂ 0) := by
    rw [cell_val y t r₂ hv]
    simp
    field_simp
    ring
  simp only []
  rw [hrow, hph]

end GlobalTheory.CompanionTheory.BigCell
