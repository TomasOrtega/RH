import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableToGLEntry
import GroundTheory.GlobalFields.TateThesis.ArchCharsUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentLowerRowsLeviSetClosedSubgroup
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem colGL_val_apply {a : ℕ} (r : ℕ) (x : Fin a → ℂ) (i j : Fin a) :
    ((colGL r x : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j =
      (1 : Matrix (Fin a) (Fin a) ℂ) i j + (if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem colGL_inv_val_apply {a : ℕ} (r : ℕ) (x : Fin a → ℂ) (i j : Fin a) :
    (((colGL r x)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j =
      (1 : Matrix (Fin a) (Fin a) ℂ) i j - (if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) := rfl

/- English proof (translation)
Apply the tactic sequence `rw [Matrix.one_apply]; split_ifs <;> simp`.
-/
theorem norm_one_apply_le' {a : ℕ} (i j : Fin a) : ‖(1 : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

/- English proof (translation)
Use `split_ifs`. Conclude with `norm_le_pi_norm x i`. Simplify using the standard rewrite rules.
-/
theorem norm_ite_apply_le {a : ℕ} (p : Prop) [Decidable p] (x : Fin a → ℂ) (i : Fin a) :
    ‖(if p then x i else 0)‖ ≤ ‖x‖ := by
  split_ifs
  · exact norm_le_pi_norm x i
  · simp

/- English proof (translation)
Unfold `htGL`. Establish `h1 : ∀ i j : Fin a, ‖((colGL r x : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ 1 + ‖x‖`. Introduce `i j`. Rewrite using `[colGL_val_apply]`. Conclude with `(norm_add_le _ _).trans (add_le_add (norm_one_apply_le' i j) (norm_ite_apply_le _ x i))`.

Establish `h2 : ∀ i j : Fin a, ‖(((colGL r x)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ 1 + ‖x‖`. Introduce `i j`. Rewrite using `[colGL_inv_val_apply]`. Conclude with `(norm_sub_le _ _).trans (add_le_add (norm_one_apply_le' i j) (norm_ite_apply_le _ x i))`. Establish `s1 : ∑ i, ∑ j, ‖((colGL r x : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ (a : ℝ) ^ 2 * (1 + ‖x‖)`.

Combine the equalities or inequalities in the displayed calculation. Establish `s2 : ∑ i, ∑ j, ‖(((colGL r x)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ (a : ℝ) ^ 2 * (1 + ‖x‖)`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem htGL_colGL_le {a : ℕ} (r : ℕ) (x : Fin a → ℂ) :
    htGL (colGL r x) ≤ 1 + 2 * (a : ℝ) ^ 2 * (1 + ‖x‖) := by
  unfold htGL
  have h1 : ∀ i j : Fin a, ‖((colGL r x : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ 1 + ‖x‖ := by
    intro i j
    rw [colGL_val_apply]
    exact (norm_add_le _ _).trans (add_le_add (norm_one_apply_le' i j) (norm_ite_apply_le _ x i))
  have h2 : ∀ i j : Fin a, ‖(((colGL r x)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ 1 + ‖x‖ := by
    intro i j
    rw [colGL_inv_val_apply]
    exact (norm_sub_le _ _).trans (add_le_add (norm_one_apply_le' i j) (norm_ite_apply_le _ x i))
  have s1 : ∑ i, ∑ j, ‖((colGL r x : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ (a : ℝ) ^ 2 * (1 + ‖x‖) := by
    calc _ ≤ ∑ _i : Fin a, ∑ _j : Fin a, (1 + ‖x‖) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have s2 : ∑ i, ∑ j, ‖(((colGL r x)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ (a : ℝ) ^ 2 * (1 + ‖x‖) := by
    calc _ ≤ ∑ _i : Fin a, ∑ _j : Fin a, (1 + ‖x‖) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h2 i j
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  linarith

/- English proof (translation)
The claim follows from `ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [Prod.norm_def]`.
-/
theorem norm_inr_le_one' (Z V : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ‖ContinuousLinearMap.inr ℝ Z V‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [Prod.norm_def]

/- English proof (translation)
The claim follows from `ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [Prod.norm_def]`.
-/
theorem norm_inl_le_one' (Z V : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ‖ContinuousLinearMap.inl ℝ Z V‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [Prod.norm_def]

end GlobalTheory.JSW
