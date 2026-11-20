import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CohomologyShapeOfTateDualityEuler
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ShapeNeg.shapeG_of_localDuality` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCohomologyShapeOfTateDualityEuler.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.cohomology_shape_of_tate_duality_euler : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ReciprocityTheory.ChartRestriction.T2.ShapeG := by
  first | exact @GlobalTheory.ShapeNeg.shapeG_of_localDuality | exact GlobalTheory.ShapeNeg.shapeG_of_localDuality | (intros; apply GlobalTheory.ShapeNeg.shapeG_of_localDuality <;> assumption)
