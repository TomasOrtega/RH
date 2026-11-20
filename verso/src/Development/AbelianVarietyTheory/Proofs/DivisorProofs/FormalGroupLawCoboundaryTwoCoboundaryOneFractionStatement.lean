import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOneFraction
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.formalGroupLawCoboundaryTwo_coboundaryOne_fractions` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFormalGroupLawCoboundaryTwoCoboundaryOneFraction.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.cob2_cob1_eq_zero_of_isLaw : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLaw μ → ∀ g : MvPowerSeries (Fin d) Q, cob2 (up Q μ) (cob1 (up Q μ) g) = 0 := by
  first | exact @GlobalTheory.formalGroupLawCoboundaryTwo_coboundaryOne_fractions | exact GlobalTheory.formalGroupLawCoboundaryTwo_coboundaryOne_fractions | (intros; apply GlobalTheory.formalGroupLawCoboundaryTwo_coboundaryOne_fractions <;> assumption)
