import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueMapOfContinuousEvaluatio
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHasPAdicPowerSeriesValueMapOfContinuousEvaluatio.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.hasPAdicPowerSeriesValue_map_of_continuousEvaluation : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ s : MvPowerSeries σ B, HasVal p z (map (algebraMap B Q) s) (algebraMap B Q (E s)) := by
  first | exact @GlobalTheory.hasVal_map_of_isEval | exact GlobalTheory.hasVal_map_of_isEval | (intros; apply GlobalTheory.hasVal_map_of_isEval <;> assumption)
