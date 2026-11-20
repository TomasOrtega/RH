import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

/- English proof (translation)
Introduce `R _ N a l hl`. Unfold `leadingMinor`. Rewrite using `[Matrix.det_of_isUpperTriangular]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Simplify using `[unipotentMatrix]`.

Introduce `i j hji`. Establish `hji' : Fin.castLE hl j < Fin.castLE hl i` using `hji`. Simplify using `only [Matrix.submatrix_apply, unipotentMatrix, Matrix.of_apply]`. Rewrite using `[dif_neg (not_lt.mpr hji'.le), if_neg (ne_of_gt hji')]`.
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
