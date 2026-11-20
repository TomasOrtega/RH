import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCast
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinProjComplete.isAdicComplete_span_natCast` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsAdicCompleteSpanNatCast.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.isAdicComplete_span_natCast_of_finite_projective' : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  first | exact @GlobalTheory.FinProjComplete.isAdicComplete_span_natCast | exact GlobalTheory.FinProjComplete.isAdicComplete_span_natCast | (intros; apply GlobalTheory.FinProjComplete.isAdicComplete_span_natCast <;> assumption)
