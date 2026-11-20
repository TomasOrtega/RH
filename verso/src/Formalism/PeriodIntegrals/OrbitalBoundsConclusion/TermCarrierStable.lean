import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermCarrierStability.TermStableHolds

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
The claim follows from `PI.TCS.termStable_holds D u u'`.
-/
theorem term_carrier_stable (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermStable D u u' :=
  PI.TCS.termStable_holds D u u'
