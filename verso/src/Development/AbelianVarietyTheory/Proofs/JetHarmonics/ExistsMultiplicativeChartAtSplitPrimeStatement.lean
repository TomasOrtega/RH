import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMultiplicativeChartAtSplitPrime
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MomOne.SplitChart.exists_mChart` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FExistsMultiplicativeChartAtSplitPrime.lean&line=207#L207)
-/
theorem _root_.GlobalTheory.T.exists_multiplicativeChart_at_splitPrime : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.Ok → IsAlgebraic ℚ M.W.a₁ → IsAlgebraic ℚ M.W.a₂ → IsAlgebraic ℚ M.W.a₃ → IsAlgebraic ℚ M.W.a₄ → IsAlgebraic ℚ M.W.a₆ → ∃ ω : ℂ_[q], M.MChart ω := by
  first | exact @GlobalTheory.MomOne.SplitChart.exists_mChart | exact GlobalTheory.MomOne.SplitChart.exists_mChart | (intros; apply GlobalTheory.MomOne.SplitChart.exists_mChart <;> assumption)
