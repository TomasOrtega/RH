import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PGaussDualMin

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem inner_toLp_eq_dotProduct {g : ℕ} (m w : Fin g → ℝ) :
    inner ℝ (WithLp.toLp 2 m : EuclideanSpace ℝ (Fin g)) (WithLp.toLp 2 w) = m ⬝ᵥ w := by
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities.
-/
theorem qf_inv_transpose_mulVec {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0)
    (m : Fin g → ℝ) : qf (Bᵀ * B)⁻¹ (Bᵀ *ᵥ m) = m ⬝ᵥ m := by
  have hBt : IsUnit (Bᵀ).det := by rw [det_transpose]; exact hB.isUnit
  have hBu : IsUnit B.det := hB.isUnit
  have h1 : (Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ m) = B⁻¹ *ᵥ m := by
    rw [Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hBt,
      Matrix.mul_one]
  unfold qf
  rw [h1, mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec, mul_nonsing_inv _ hBu,
    one_mulVec]

end PGaussDualMin

open PGaussDualMin in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GaussDualMin.proof : GaussDualMin.Statement := by
  intro g B hB μ hμ hμ0
  classical
  obtain ⟨m, rfl⟩ : ∃ m : Fin g → ℝ, μ = WithLp.toLp 2 m := ⟨WithLp.ofLp μ, (WithLp.toLp_ofLp _ μ).symm⟩
  have hdual := GroundTheory.Global.mem_dualLattice.1 hμ
  have hex : ∀ i : Fin g, ∃ k : ℤ, inner ℝ (WithLp.toLp 2 m : EuclideanSpace ℝ (Fin g))
      (WithLp.toLp 2 (B *ᵥ Pi.single i 1)) = k :=
    fun i => hdual _ (Submodule.subset_span ⟨i, rfl⟩)
  choose l hl using hex
  have hlm : intVec l = Bᵀ *ᵥ m := by
    funext i
    change ((l i : ℤ) : ℝ) = _
    rw [← hl i, inner_toLp_eq_dotProduct, dotProduct_mulVec, dotProduct_single_one,
      mulVec_transpose]
  refine ⟨l, ?_, ?_⟩
  · intro hl0
    apply hμ0
    have hBt : IsUnit (Bᵀ).det := by rw [det_transpose]; exact hB.isUnit
    have h0 : Bᵀ *ᵥ m = 0 := by
      rw [← hlm, hl0]; funext i; simp [intVec]
    have hm0 : m = 0 := by
      calc m = (Bᵀ)⁻¹ *ᵥ (Bᵀ *ᵥ m) := by
            rw [mulVec_mulVec, nonsing_inv_mul _ hBt, one_mulVec]
        _ = 0 := by rw [h0, mulVec_zero]
    rw [hm0]; rfl
  · rw [hlm, qf_inv_transpose_mulVec B hB, ← real_inner_self_eq_norm_sq,
      inner_toLp_eq_dotProduct]

end GroundTheory.Heights₂.Heights
