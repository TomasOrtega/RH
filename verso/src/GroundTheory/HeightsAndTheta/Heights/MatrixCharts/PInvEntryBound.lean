import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace MCInvEntryBound

/- English proof (translation)
Simplify using `[mulVec_single, single_dotProduct]`.
-/
theorem single_dot_mulVec_single {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (j l : ι) : Pi.single j (1 : ℝ) ⬝ᵥ (A *ᵥ Pi.single l 1) = A j l := by
  simp [mulVec_single, single_dotProduct]

/- English proof (translation)
Establish `hinv : (Y⁻¹).PosSemidef` using `(MCBounds.posDef_of_ge hc h).inv.posSemidef`. Establish `hle` using `MCBounds.quad_nonneg (MCBounds.inv_le_of_ge hc h) (Pi.single j 1)`. Establish `hge` using `MCBounds.quad_nonneg hinv (Pi.single j 1)`. Rewrite `hle`, `hge` using `[single_dot_mulVec_single]`. Use `⟨hge, ?_⟩` and prove the remaining obligations.

Simplify `hle` using `[Matrix.sub_apply, Matrix.smul_apply]`.
-/
theorem inv_diag_bounds {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 < c) (h : (Y - c • (1 : Matrix ι ι ℝ)).PosSemidef) (j : ι) :
    0 ≤ Y⁻¹ j j ∧ Y⁻¹ j j ≤ c⁻¹ := by
  have hinv : (Y⁻¹).PosSemidef := (MCBounds.posDef_of_ge hc h).inv.posSemidef
  have hle := MCBounds.quad_nonneg (MCBounds.inv_le_of_ge hc h) (Pi.single j 1)
  have hge := MCBounds.quad_nonneg hinv (Pi.single j 1)
  rw [single_dot_mulVec_single] at hle hge
  refine ⟨hge, ?_⟩
  simpa [Matrix.sub_apply, Matrix.smul_apply] using hle

end MCInvEntryBound

/- English proof (translation)
Introduce `g Y c hc h j l`. Establish `hinv : (Y⁻¹).PosSemidef` using `(MCBounds.posDef_of_ge hc h).inv.posSemidef`. Establish `hcs` using `MCBounds.quad_cs hinv (Pi.single j 1) (Pi.single l 1)`. Simplify using `only [MCInvEntryBound.single_dot_mulVec_single] at hcs`. Take `⟨hj0, hj⟩` from `MCInvEntryBound.inv_diag_bounds hc h j`.

Take `⟨hl0, hl⟩` from `MCInvEntryBound.inv_diag_bounds hc h l`. Establish `hci : 0 ≤ c⁻¹` using `inv_nonneg.mpr hc.le`. Establish `hsq : (Y⁻¹ j l) ^ 2 ≤ c⁻¹ ^ 2`. Combine the equalities or inequalities in the displayed calculation. Conclude with `abs_le_of_sq_le_sq' hsq hci |> fun h => abs_le.mpr h`.
-/
theorem InvEntryBound.proof : InvEntryBound.Statement := by
  intro g Y c hc h j l
  have hinv : (Y⁻¹).PosSemidef := (MCBounds.posDef_of_ge hc h).inv.posSemidef
  have hcs := MCBounds.quad_cs hinv (Pi.single j 1) (Pi.single l 1)
  simp only [MCInvEntryBound.single_dot_mulVec_single] at hcs
  obtain ⟨hj0, hj⟩ := MCInvEntryBound.inv_diag_bounds hc h j
  obtain ⟨hl0, hl⟩ := MCInvEntryBound.inv_diag_bounds hc h l
  have hci : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hsq : (Y⁻¹ j l) ^ 2 ≤ c⁻¹ ^ 2 := by
    calc (Y⁻¹ j l) ^ 2 ≤ Y⁻¹ j j * Y⁻¹ l l := hcs
      _ ≤ c⁻¹ * c⁻¹ := mul_le_mul hj hl hl0 hci
      _ = c⁻¹ ^ 2 := (sq _).symm
  exact abs_le_of_sq_le_sq' hsq hci |> fun h => abs_le.mpr h

end

end GroundTheory.Heights₂.Heights
