import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLocalDualityOfLocalTateDuality
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ratIso_of_localTateDuality` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FRationalLocalDualityOfLocalTateDuality.lean&line=293#L293)
-/
theorem _root_.GlobalTheory.T.rationalLocalDuality_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.RatIso := by
  first | exact @GlobalTheory.ratIso_of_localTateDuality | exact GlobalTheory.ratIso_of_localTateDuality | (intros; apply GlobalTheory.ratIso_of_localTateDuality <;> assumption)
