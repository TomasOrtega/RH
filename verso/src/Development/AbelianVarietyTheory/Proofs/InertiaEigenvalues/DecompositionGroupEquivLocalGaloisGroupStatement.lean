import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DecLocal.decEquiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDecompositionGroupEquivLocalGaloisGroup.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.decomposition_group_equiv_local_galois_group : ReciprocityTheory.ChartRestriction.T2.DecEquiv := by
  first | exact @GlobalTheory.DecLocal.decEquiv | exact GlobalTheory.DecLocal.decEquiv | (intros; apply GlobalTheory.DecLocal.decEquiv <;> assumption)
