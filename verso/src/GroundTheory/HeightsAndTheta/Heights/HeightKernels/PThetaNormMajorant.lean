import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsTheta
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ThetaGauss
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

namespace KThetaNormMajorant

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem isSymm_of_posDef {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) : Y.IsSymm := by
  have h := hY.isHermitian
  unfold Matrix.IsHermitian at h
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

end KThetaNormMajorant

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Rewrite the conclusion repeatedly using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Reduce the equality to equality of the corresponding arguments.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ThetaNormMajorant.proof (h : ThetaSummandNorm.Statement) : ThetaNormMajorant.Statement := by
  intro g X Y a b u₁ u₂ hY
  have hS := KThetaNormMajorant.isSymm_of_posDef hY
  set z : Fin g → ℂ := periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ) with hz
  set E : ℝ := exp (-π * qf Y u₁) with hE
  have hEpos : 0 < E := exp_pos _
  have hterm : ∀ k : Fin g → ℤ,
      ‖thetaSummand X Y a b z k‖ = exp (-π * qf Y (intVec k + a + u₁)) * E⁻¹ := by
    intro k
    rw [← h g X Y a b u₁ u₂ k hS, mul_inv_cancel_right₀ hEpos.ne']
  have hG : Summable fun k : Fin g → ℤ => exp (-π * qf Y (intVec k + a + u₁)) := by
    have := KTheta.summable_exp_qf Y hY π Real.pi_pos (a + u₁)
    simpa only [add_assoc] using this
  have hsum : Summable fun k : Fin g → ℤ => ‖thetaSummand X Y a b z k‖ := by
    simp_rw [hterm]
    exact hG.mul_right _
  have hN : thetaNorm X Y a b u₁ u₂ = ‖∑' k, thetaSummand X Y a b z k‖ * E := rfl
  rw [hN]
  calc ‖∑' k, thetaSummand X Y a b z k‖ * E
      ≤ (∑' k, ‖thetaSummand X Y a b z k‖) * E :=
        mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hsum) hEpos.le
    _ = ∑' k, ‖thetaSummand X Y a b z k‖ * E := (tsum_mul_right).symm
    _ = ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁)) := by
        congr 1; funext k
        rw [hterm, inv_mul_cancel_right₀ hEpos.ne']

end GroundTheory.Heights₂.Heights
