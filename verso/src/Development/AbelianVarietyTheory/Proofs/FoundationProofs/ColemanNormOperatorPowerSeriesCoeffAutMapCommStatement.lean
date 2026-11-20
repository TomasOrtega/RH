import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColemanNormOperatorPowerSeriesCoeffAutMapComm
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FColemanNormOperatorPowerSeriesCoeffAutMapComm.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.colemanNormOperator_powerSeriesCoeffAutMap_comm : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R) (h : PowerSeries R), normOp p (smap σ h) = smap σ (normOp p h) := by
  first | exact @GlobalTheory.Col.NormCoeff.normOp_smap | exact GlobalTheory.Col.NormCoeff.normOp_smap | (intros; apply GlobalTheory.Col.NormCoeff.normOp_smap <;> assumption)
