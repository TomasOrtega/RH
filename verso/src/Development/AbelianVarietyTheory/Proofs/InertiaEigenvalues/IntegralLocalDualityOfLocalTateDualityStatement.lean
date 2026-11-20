import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralLocalDualityOfLocalTateDuality
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIntegralLocalDualityOfLocalTateDuality.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.integral_localDuality_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.IntIso := by
  first | exact @GlobalTheory.LocDualInt.int_iso_of_localTateDuality | exact GlobalTheory.LocDualInt.int_iso_of_localTateDuality | (intros; apply GlobalTheory.LocDualInt.int_iso_of_localTateDuality <;> assumption)
