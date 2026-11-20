import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace KLinesGramChange

noncomputable def colMatrix {K : Type*} [Field K] {n : ℕ} (σ : K →+* ℂ) {ι : Type*}
    (u : ι → Fin n → K) : Matrix (Fin n) ι ℂ :=
  Matrix.of fun j a => σ (u a j)

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gramAt_eq {K : Type*} [Field K] {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ)
    {ι : Type*} [Fintype ι] (u : ι → Fin n → K) :
    gramAt h σ u = (colMatrix σ u)ᴴ * h * colMatrix σ u := by
  ext a b
  simp only [gramAt, embVec, colMatrix, Matrix.mul_apply, dotProduct, mulVec,
    conjTranspose_apply, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem colMatrix_transform {K : Type*} [Field K] {n : ℕ} (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    (u : ι → Fin n → K) (P : Matrix ι ι K) :
    colMatrix σ (fun a => ∑ b, P b a • u b) = colMatrix σ u * P.map σ := by
  ext j a
  simp only [colMatrix, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

end KLinesGramChange

open KLinesGramChange in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem LinesGramChange.proof : LinesGramChange.Statement := by
  intro K _ n h σ ι _ u P
  rw [gramAt_eq, gramAt_eq, colMatrix_transform, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end GroundTheory.Heights₂.Heights
