import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedPadicDecompositionHomExists
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnramifiedPadicDecompositionHomExists.lean&line=218#L218)
-/
theorem _root_.GlobalTheory.T.unramified_padic_decomposition_hom_exists : ReciprocityTheory.ChartRestriction.T2.UnrDec := by
  first | exact @GlobalTheory.UnrChar.unrDec | exact GlobalTheory.UnrChar.unrDec | (intros; apply GlobalTheory.UnrChar.unrDec <;> assumption)
