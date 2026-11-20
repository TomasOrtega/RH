import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.IntegralityAtFormsOfAway
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.AwayCore

namespace PI.IntegralAtBasePointLattice

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem integral_at_t0_lattice : ∀ (D : Formalism.BasicNotions.D7) (u : D.what₂.Word), Formalism.MainNotions.RT.IntegralityLevelZeroUnderForms D u :=
  PI.UnitaryGroupMassFormula.IAT.integrality_at_forms_of_away (fun _ _ T _ _ _ => PI.UnitaryGroupMassFormula.IAT.lattices_away_from_place T)

end PI.IntegralAtBasePointLattice
