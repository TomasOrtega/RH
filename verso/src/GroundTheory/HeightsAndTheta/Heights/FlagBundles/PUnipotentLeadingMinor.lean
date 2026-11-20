import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem UnipotentLeadingMinor.proof : UnipotentLeadingMinor.Statement := by
  intro R _ N a l hl
  unfold leadingMinor
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [unipotentMatrix]
  · intro i j hji
    have hji' : Fin.castLE hl j < Fin.castLE hl i := hji
    simp only [Matrix.submatrix_apply, unipotentMatrix, Matrix.of_apply]
    rw [dif_neg (not_lt.mpr hji'.le), if_neg (ne_of_gt hji')]

end GroundTheory.Heights₂.Heights.FlagBundles
