import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesTranslateNormLe
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MomOne.TransNorm.translate_norm_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FCpTransportedTaylorSeriesTranslateNormLe.lean&line=137#L137)
-/
theorem _root_.GlobalTheory.T.cpTransportedTaylorSeries_translate_norm_le : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (φ : ℂ → ℂ) (t : ℂ) (B : ℝ), M.Chart ℓ → Ell M.L φ → AnalyticAt ℂ φ 0 → AnalyticAt ℂ φ t → (∀ p, meromorphicOrderAt φ p < 0 → ¬ M.Small p) → ¬ M.Small t → Bdd (hat M.ι ℓ (fun z => φ (z + t))) → Bd B (hat M.ι ℓ φ) → Bd B (hat M.ι ℓ (fun z => φ (z + t))) := by
  first | exact @GlobalTheory.MomOne.TransNorm.translate_norm_le | exact GlobalTheory.MomOne.TransNorm.translate_norm_le | (intros; apply GlobalTheory.MomOne.TransNorm.translate_norm_le <;> assumption)
