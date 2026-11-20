import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLimsupShiftLe
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GrowthShift.growth_shift_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRankGrowthLimsupShiftLe.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.rankGrowthLimsup_shift_le : ∀ (D e : ℕ) (r : ℕ → ℕ∞), growth D (fun k => r (k + e)) ≤ growth D r := by
  first | exact @GlobalTheory.GrowthShift.growth_shift_le | exact GlobalTheory.GrowthShift.growth_shift_le | (intros; apply GlobalTheory.GrowthShift.growth_shift_le <;> assumption)
