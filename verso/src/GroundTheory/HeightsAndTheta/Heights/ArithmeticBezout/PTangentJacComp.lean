import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsTangentJacComp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem TangentJacComp.real_inner_eq_re {d : ℕ} (x y : EuclideanSpace ℂ (Fin d)) :
    @inner ℝ _ _ x y = RCLike.re (@inner ℂ _ _ x y) := by
  simp [PiLp.inner_apply, Complex.inner, map_sum]

/- English proof (translation)
Use symmetry to reverse the relation. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem TangentJacComp.adjoint_restrictScalars {d n : ℕ}
    (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    LinearMap.adjoint (L.restrictScalars ℝ) = (LinearMap.adjoint L).restrictScalars ℝ := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [TangentJacComp.real_inner_eq_re, TangentJacComp.real_inner_eq_re]
  simp [LinearMap.adjoint_inner_left]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem TangentJacComp.areaJacobian_eq {d n : ℕ}
    (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    areaJacobian (L.restrictScalars ℝ) = L.normDet ^ 2 := by
  have hsq : ((L.normDet ^ 2 : ℝ) : ℂ) = LinearMap.det (LinearMap.adjoint L ∘ₗ L) := L.normDet_sq
  rw [areaJacobian, TangentJacComp.adjoint_restrictScalars]
  have hc : (LinearMap.adjoint L).restrictScalars ℝ ∘ₗ L.restrictScalars ℝ =
      (LinearMap.adjoint L ∘ₗ L).restrictScalars ℝ := rfl
  rw [hc, LinearMap.det_restrictScalars, ← hsq, Algebra.norm_complex_apply, Complex.normSq_ofReal,
    Real.sqrt_mul_self (by positivity)]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem TangentJacComp.proof : TangentJacComp.Statement := by
  intro d n L π
  have hc := LinearMap.normDet_comp L (linProjₗ π)
  have hr : |LinearMap.det (((linProjₗ π).comp L).restrictScalars ℝ)| =
      ((linProjₗ π).comp L).normDet ^ 2 := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, LinearMap.normDet_eq_norm_det,
      Complex.sq_norm, abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [hr, hc, tangentJac, TangentJacComp.areaJacobian_eq]
  rw [mul_pow]
  rfl

end

end GroundTheory.Heights₂.Heights
