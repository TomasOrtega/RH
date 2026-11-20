import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiLogarithmModIdealTopLinearCombination
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QLog.ql_comb_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsQuasiLogarithmModIdealTopLinearCombination.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.isQuasiLogarithmModIdeal_top_linearCombination : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → ∀ w : ι → B, QL μ ⊤ (comb w e) := by
  first | exact @GlobalTheory.QLog.ql_comb_top | exact GlobalTheory.QLog.ql_comb_top | (intros; apply GlobalTheory.QLog.ql_comb_top <;> assumption)
