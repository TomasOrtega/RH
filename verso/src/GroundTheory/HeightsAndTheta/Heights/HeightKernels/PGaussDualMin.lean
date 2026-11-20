import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PGaussDualMin

/- English proof (translation)
Rewrite using `[EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]`.
-/
theorem inner_toLp_eq_dotProduct {g : ℕ} (m w : Fin g → ℝ) :
    inner ℝ (WithLp.toLp 2 m : EuclideanSpace ℝ (Fin g)) (WithLp.toLp 2 w) = m ⬝ᵥ w := by
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]

/- English proof (translation)
Establish `hBt : IsUnit (Bᵀ).det` using `by rw [det_transpose]; exact hB.isUnit`. Establish `hBu : IsUnit B.det` using `hB.isUnit`. Establish `h1 : (Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ m) = B⁻¹ *ᵥ m`. Rewrite using `[Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hBt, Matrix.mul_one]`. Unfold `qf`.

Rewrite using `[h1, mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec, mul_nonsing_inv _ hBu, one_mulVec]`.
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
Introduce `g B hB μ hμ hμ0`. Take `⟨m, rfl⟩ : ∃ m : Fin g → ℝ, μ = WithLp.toLp 2 m` from `⟨WithLp.ofLp μ, (WithLp.toLp_ofLp _ μ).symm⟩`. Establish `hdual` using `GroundTheory.Global.mem_dualLattice.1 hμ`. Establish `hex : ∀ i : Fin g, ∃ k : ℤ, inner ℝ (WithLp.toLp 2 m : EuclideanSpace ℝ (Fin g)) (WithLp.toLp 2 (B *ᵥ Pi.single i 1)) = k` using `fun i => hdual _ (Submodule.subset_span ⟨i, rfl⟩)`. Use `choose l hl using hex`.

Establish `hlm : intVec l = Bᵀ *ᵥ m`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `((l i : ℤ) : ℝ) = _`. Rewrite using `[← hl i, inner_toLp_eq_dotProduct, dotProduct_mulVec, dotProduct_single_one, mulVec_transpose]`. Use `⟨l, ?_, ?_⟩` and prove the remaining obligations.

Introduce `hl0`. Apply `hμ0` to reduce the goal to its premises. Establish `hBt : IsUnit (Bᵀ).det` using `by rw [det_transpose]; exact hB.isUnit`. Establish `h0 : Bᵀ *ᵥ m = 0`. Rewrite using `[← hlm, hl0]`.

Use function extensionality and compare the values at `i`. Simplify using `[intVec]`. Establish `hm0 : m = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mulVec_mulVec, nonsing_inv_mul _ hBt, one_mulVec]`.

Use `_ = 0 := by rw [h0, mulVec_zero]`. Rewrite using `[hm0]`. Both sides reduce to the same expression. Rewrite using `[hlm, qf_inv_transpose_mulVec B hB, ← real_inner_self_eq_norm_sq, inner_toLp_eq_dotProduct]`.
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
