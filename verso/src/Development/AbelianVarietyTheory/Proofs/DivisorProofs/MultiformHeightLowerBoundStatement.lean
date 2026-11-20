import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiformHeightLowerBound
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HtLowProof.htLow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMultiformHeightLowerBound.lean&line=107#L107)
-/
theorem _root_.GlobalTheory.T.multiformHeight_lowerBound : HtLow := by
  first | exact @GlobalTheory.HtLowProof.htLow | exact GlobalTheory.HtLowProof.htLow | (intros; apply GlobalTheory.HtLowProof.htLow <;> assumption)
