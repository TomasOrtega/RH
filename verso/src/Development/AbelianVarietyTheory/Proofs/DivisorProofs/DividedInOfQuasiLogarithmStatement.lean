import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedInOfQuasiLogarithm
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QLogDiff.dIn_of_QL` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDividedInOfQuasiLogarithm.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.divided_in_of_quasi_logarithm : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), QL μ N f → DIn N f := by
  first | exact @GlobalTheory.QLogDiff.dIn_of_QL | exact GlobalTheory.QLogDiff.dIn_of_QL | (intros; apply GlobalTheory.QLogDiff.dIn_of_QL <;> assumption)
