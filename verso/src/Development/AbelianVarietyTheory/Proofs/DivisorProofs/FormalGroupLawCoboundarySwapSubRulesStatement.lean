import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundarySwapSubRules
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFormalGroupLawCoboundarySwapSubRules.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.formalGroupLawCoboundary_swap_sub_rules : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (c c' : MvPowerSeries (Fin d ⊕ Fin d) R) (f f' : MvPowerSeries (Fin d) R), cob2 μ (c - c') = cob2 μ c - cob2 μ c' ∧ swap (c - c') = swap c - swap c' ∧ cob1 μ (f - f') = cob1 μ f - cob1 μ f' := by
  first | exact @GlobalTheory.CobLin.sub_rules | exact GlobalTheory.CobLin.sub_rules | (intros; apply GlobalTheory.CobLin.sub_rules <;> assumption)
