import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.ExactSecondDegreeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.DivisionPartitionTotal

noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem sgn_one {D : ℕ} (i : Fin D) (J : Finset (Fin D)) (h : ∀ l ∈ J, ¬ l < i) : sgn i J = 1 := by
  unfold sgn
  rw [Finset.filter_eq_empty_iff.mpr h]; simp

end PI.EagonNorthcottZ
