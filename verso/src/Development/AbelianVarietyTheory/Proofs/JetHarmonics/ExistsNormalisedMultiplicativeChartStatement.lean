import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormalisedMultiplicativeChart
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FExistsNormalisedMultiplicativeChart.lean&line=200#L200)
-/
theorem _root_.GlobalTheory.T.exists_normalised_multiplicativeChart : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → ∃ a : ℤ_[q], ‖a‖ = 1 ∧ M.MChart (ω * zc a) ∧ ∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ M.At (ω * zc a) (M.ι (kap1 d 1 y)) y := by
  first | exact @GlobalTheory.MomOne.Norm.exists_normalised_chart | exact GlobalTheory.MomOne.Norm.exists_normalised_chart | (intros; apply GlobalTheory.MomOne.Norm.exists_normalised_chart <;> assumption)
