import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePrimeValuationSumEqLogGapFamily
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TypeValNN.typePrime_valuationSum_eq_logGap_family` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTypePrimeValuationSumEqLogGapFamily.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.normDecompositionCond_famP : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.NormDecompositionCond (Fm.D x i) (Fm.ex x hx i).errX := by
  first | exact @GlobalTheory.TypeValNN.typePrime_valuationSum_eq_logGap_family | exact GlobalTheory.TypeValNN.typePrime_valuationSum_eq_logGap_family | (intros; apply GlobalTheory.TypeValNN.typePrime_valuationSum_eq_logGap_family <;> assumption)
