import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open Matrix
open scoped ComplexOrder MatrixOrder

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem HermitianDetMono.one_le_det_one_add {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.PosSemidef) : 1 ≤ (1 + M).det := by
  have hH : (1 + M).IsHermitian := isHermitian_one.add hM.isHermitian
  have hev : ∀ i, (1 : ℝ) ≤ hH.eigenvalues i := by
    intro i
    rw [hH.eigenvalues_eq i]
    have hv : star ⇑(hH.eigenvectorBasis i) ⬝ᵥ ⇑(hH.eigenvectorBasis i) = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        hH.eigenvectorBasis.orthonormal.1 i]
      simp
    rw [add_mulVec, one_mulVec, dotProduct_add, map_add, hv, RCLike.one_re]
    linarith [hM.re_dotProduct_nonneg (hH.eigenvectorBasis i)]
  rw [hH.det_eq_prod_eigenvalues]
  have hprod : (1 : ℝ) ≤ ∏ i, hH.eigenvalues i := by
    calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
      _ ≤ ∏ i, hH.eigenvalues i :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => hev i)
  have key : ((1 : ℝ) : ℂ) ≤ ((∏ i, hH.eigenvalues i : ℝ) : ℂ) := Complex.real_le_real.mpr hprod
  convert key using 1
  · simp
  · simp [Complex.ofReal_prod]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the argument to an intermediate assertion. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem HermitianDetMono.proof : HermitianDetMono.Statement := by
  intro n A B hB hAB
  have hA : A.PosSemidef := by simpa using hB.add hAB
  suffices h : B.det ≤ A.det from (Complex.le_def.mp h).1
  by_cases hdet : B.det = 0
  · rw [hdet]; exact hA.det_nonneg
  · obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
    have hy : IsUnit y.det := by
      rw [det_mul] at hdet
      exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
    set M := (y⁻¹)ᴴ * (A - star y * y) * y⁻¹ with hMdef
    have hM : M.PosSemidef := hAB.conjTranspose_mul_mul_same y⁻¹
    have hfac : A = star y * (1 + M) * y := by
      have h1 : star y * (y⁻¹)ᴴ = 1 := by
        rw [star_eq_conjTranspose, ← conjTranspose_mul, nonsing_inv_mul y hy, conjTranspose_one]
      rw [hMdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc,
        nonsing_inv_mul y hy, Matrix.mul_one]
      abel
    have hdA : A.det = (1 + M).det * (star y * y).det := by
      conv_lhs => rw [hfac]
      rw [det_mul, det_mul, det_mul]; ring
    rw [hdA]
    exact le_mul_of_one_le_left hB.det_nonneg (HermitianDetMono.one_le_det_one_add hM)

end GroundTheory.Heights₂.Heights.FourB
