import Formalism.PeriodIntegrals.OrbRestr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetRestriction.OrbitRestriction

/- English proof (translation)
The claim follows from `PI.OrbJet.OrbW.orbitRestriction`.
-/
theorem PI.OrbRestr : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitRestriction E :=
  PI.OrbJet.OrbW.orbitRestriction
