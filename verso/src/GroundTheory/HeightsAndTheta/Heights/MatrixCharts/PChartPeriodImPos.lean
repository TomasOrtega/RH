import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

/- English proof (translation)
Introduce `D z hz ℓ hℓ`. Rewrite using `[MCPeriod.period_im D z ℓ hℓ]`. Establish `hY : (D.Y z - D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ)).PosSemidef` using `D.Y_ge z hz`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e : D.Y z = (D.Y z - D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ)) + D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ)` using `by abel`.

Rewrite using `[e]`. Conclude with `Matrix.PosDef.posSemidef_add hY (PosDef.one.smul D.c_pos)`. Introduce `x`. Establish `h` using `hY.dotProduct_mulVec_nonneg x`. Simplify using `only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul] at h`.

Establish `hx : x ⬝ᵥ x = ∑ k, x k ^ 2`. Simplify using `only [dotProduct, sq]`. Rewrite `h` using `[hx]`. Rewrite using `[MCSchur.qf]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ChartPeriodImPos.proof : ChartPeriodImPos.Statement := by
  intro D z hz ℓ hℓ
  rw [MCPeriod.period_im D z ℓ hℓ]
  have hY : (D.Y z - D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ)).PosSemidef := D.Y_ge z hz
  refine ⟨?_, ?_⟩
  · have e : D.Y z = (D.Y z - D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ)) +
        D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) := by abel
    rw [e]
    exact Matrix.PosDef.posSemidef_add hY (PosDef.one.smul D.c_pos)
  · intro x
    have h := hY.dotProduct_mulVec_nonneg x
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec,
      dotProduct_smul, smul_eq_mul] at h
    have hx : x ⬝ᵥ x = ∑ k, x k ^ 2 := by
      simp only [dotProduct, sq]
    rw [hx] at h
    rw [MCSchur.qf]
    linarith

end

end GroundTheory.Heights₂.Heights
