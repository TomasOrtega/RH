import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueSubMemPdIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHasPAdicPowerSeriesValueSubMemPdIdeal.lean&line=170#L170)
-/
theorem _root_.GlobalTheory.T.hasPAdicPowerSeriesValue_sub_mem_pd_ideal : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (z' : σ → B) (f : MvPowerSeries σ Q) (q q' : Q), (∀ i, z i - z' i ∈ J) → DIn (⊤ : Ideal B) f → HasVal p z f q → HasVal p z' f q' → ∀ m : ℕ, ∃ b ∈ J, ∃ b' : B, q - q' = algebraMap B Q (b + p ^ m * b') := by
  first | exact @GlobalTheory.HasValCong.hasVal_sub_mem | exact GlobalTheory.HasValCong.hasVal_sub_mem | (intros; apply GlobalTheory.HasValCong.hasVal_sub_mem <;> assumption)
