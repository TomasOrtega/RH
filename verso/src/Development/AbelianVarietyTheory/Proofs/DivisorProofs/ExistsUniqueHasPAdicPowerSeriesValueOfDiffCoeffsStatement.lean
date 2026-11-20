import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHasPAdicPowerSeriesValueOfDiffCoeffs
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsUniqueHasPAdicPowerSeriesValueOfDiffCoeffs.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.existsUnique_hasPAdicPowerSeriesValue_of_diffCoeffs : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ f : MvPowerSeries σ Q, DIn (⊤ : Ideal B) f → ∃! q : Q, HasVal p z f q := by
  first | exact @GlobalTheory.QLog.existsUnique_hasVal_of_dIn | exact GlobalTheory.QLog.existsUnique_hasVal_of_dIn | (intros; apply GlobalTheory.QLog.existsUnique_hasVal_of_dIn <;> assumption)
