import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.DecLocal.decEquiv | exact GlobalTheory.DecLocal.decEquiv | (intros; apply GlobalTheory.DecLocal.decEquiv <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.decomposition_group_equiv_local_galois_group : ReciprocityTheory.ChartRestriction.T2.DecEquiv := by
  first | exact @GlobalTheory.DecLocal.decEquiv | exact GlobalTheory.DecLocal.decEquiv | (intros; apply GlobalTheory.DecLocal.decEquiv <;> assumption)
