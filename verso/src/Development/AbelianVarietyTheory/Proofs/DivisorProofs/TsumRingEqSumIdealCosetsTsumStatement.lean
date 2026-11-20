import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumRingEqSumIdealCosetsTsum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbAApply
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.cosets_main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTsumRingEqSumIdealCosetsTsum.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.tsum_ring_eq_sum_ideal_cosets_tsum : ∀ (R : Type) [CommRing R] (M : Ideal R) [Fintype (R ⧸ M)] (h : R → ℂ), Summable h → ∑' α, h α = ∑ c : R ⧸ M, ∑' μ : M, h (Quotient.out c + μ) := by
  first | exact @GlobalTheory.cosets_main | exact GlobalTheory.cosets_main | (intros; apply GlobalTheory.cosets_main <;> assumption)
