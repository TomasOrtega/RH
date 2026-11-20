import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentIdealPowFinrankEqSpanDiscr
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDifferentIdealPowFinrankEqSpanDiscr.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.differentIdeal_pow_finrank_eq_span_discr' : ∀ (F : Type) [Field F] [NumberField F] [IsGalois ℚ F], differentIdeal ℤ (𝓞 F) ^ Module.finrank ℚ F = Ideal.span {((discr F : ℤ) : 𝓞 F)} := by
  first | exact @GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr | exact GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr | (intros; apply GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr <;> assumption)
