import Mathlib
import Formalism.PeriodIntegrals.LocDensCorank
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.SplitCount
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.EulerFactorTwo
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.CongruenceDensity

open ValuativeRel Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocDensCorank

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem locDensCorank_of (hC : CongStep) (hF : FieldCount) (hS : SplitCount) :
    PI.LocDensCorank.LocDensCorank := by
  intro F E _ _ _ _ _ _ _ M hloc hchar V _ _ H Λ hsd ϖ hϖ ι _ _ A a hA hdet hcard
  rw [hC F E M V H Λ ϖ ι A a hA hdet]
  by_cases hE : ∀ x : E, x ≠ 0 → IsUnit x
  · rw [if_pos hE]
    exact hF F E M hloc hchar hE V H Λ hsd ϖ hϖ ι a hcard
  · rw [if_neg hE]
    exact hS F E M hloc hchar ((PI.UnitaryGroupMassFormula.CntFormula.locE_isUnit_or_exists_algEquiv_prod_swap M.L).resolve_left hE) V H Λ hsd ϖ hϖ ι a hcard

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem locDensCorank_of_counts (hF : FieldCount) (hS : SplitCount) : PI.LocDensCorank.LocDensCorank := by
  exact locDensCorank_of congruence_density hF hS

end PI.UnitaryGroupMassFormula.LocDensCorank
