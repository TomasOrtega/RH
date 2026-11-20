import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodLocalVolumeFactorLeZeta
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorProductBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorLowerBound
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EulerLocVol.tprod_locFactor_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTprodLocalVolumeFactorLeZeta.lean&line=128#L128)
-/
theorem _root_.GlobalTheory.T.tprod_local_volume_factor_le_zeta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), 2 ≤ r → Multipliable (GlobalTheory.SUVol.locFactor E r) → ∏' v, GlobalTheory.SUVol.locFactor E r v ≤ (∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ ReciprocityTheory.ChartRestriction.G.FD.fdeg E := by
  first | exact @GlobalTheory.EulerLocVol.tprod_locFactor_le | exact GlobalTheory.EulerLocVol.tprod_locFactor_le | (intros; apply GlobalTheory.EulerLocVol.tprod_locFactor_le <;> assumption)
