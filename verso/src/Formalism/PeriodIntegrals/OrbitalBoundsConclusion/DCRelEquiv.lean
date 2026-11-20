import Mathlib
import Formalism.PeriodIntegrals.DCRelEquiv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelativeEquivalence.DCRelEquivAllHolds

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `F0 Λ _`. Conclude with `PI.DCRelEquiv.UnitaryGroupMassFormula.eqIffAll_holds _ _ _ _ _ _ _ _`.
-/
theorem term_eq_iff_relation (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermEqIff D u u' := by
  intro F0 Λ _
  exact PI.DCRelEquiv.UnitaryGroupMassFormula.eqIffAll_holds _ _ _ _ _ _ _ _
