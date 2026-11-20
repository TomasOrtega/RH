import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartHatCoeffBounds
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MomOne.Transl.translate_integral` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FChartHatCoeffBounds.lean&line=201#L201)
-/
theorem _root_.GlobalTheory.T.chart_hat_coeff_bounds : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (t : ℂ), M.Chart ℓ → ¬ M.Small t → Bd 1 (hat M.ι ℓ (fun z => M.x (z + t))) ∧ Bd 1 (hat M.ι ℓ (fun z => M.y (z + t))) ∧ ∀ r : ℝ, r < 1 → ∃ n, 0 < n ∧ r < ‖coeff n (hat M.ι ℓ (fun z => M.x (z + t)))‖ := by
  first | exact @GlobalTheory.MomOne.Transl.translate_integral | exact GlobalTheory.MomOne.Transl.translate_integral | (intros; apply GlobalTheory.MomOne.Transl.translate_integral <;> assumption)
