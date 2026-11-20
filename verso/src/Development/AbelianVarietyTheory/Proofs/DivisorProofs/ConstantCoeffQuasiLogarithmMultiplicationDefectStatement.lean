import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffQuasiLogarithmMultiplicationDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QLogDefect.constantCoeff_defect` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FConstantCoeffQuasiLogarithmMultiplicationDefect.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.constantCoeff_quasiLogarithmMultiplicationDefect : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ f : MvPowerSeries (Fin d) Q, QL μ ⊤ f → ∀ n : ℕ, constantCoeff (defect μ n f) = 0 := by
  first | exact @GlobalTheory.QLogDefect.constantCoeff_defect | exact GlobalTheory.QLogDefect.constantCoeff_defect | (intros; apply GlobalTheory.QLogDefect.constantCoeff_defect <;> assumption)
