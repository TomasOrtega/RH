import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstHasSumAndBounds
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConvSer.csub_hasSum_and_bounds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FMvPowerSeriesConvergentSubstHasSumAndBounds.lean&line=106#L106)
-/
theorem _root_.GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ τ : Type) [Fintype σ] (s : σ → MvPowerSeries τ K) (S : MvPowerSeries σ K), (∀ i, Small (s i)) → Bdd S → (∀ μ, HasSum (fun ν : σ →₀ ℕ => MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, s i ^ ν i)) (MvPowerSeries.coeff μ (csub s S))) ∧ Bdd (csub s S) ∧ (Intg S → Intg (csub s S)) ∧ (Intg S → MvPowerSeries.constantCoeff S = 0 → Small (csub s S)) := by
  first | exact @GlobalTheory.ConvSer.csub_hasSum_and_bounds | exact GlobalTheory.ConvSer.csub_hasSum_and_bounds | (intros; apply GlobalTheory.ConvSer.csub_hasSum_and_bounds <;> assumption)
