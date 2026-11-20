import Mathlib
import Formalism.PeriodIntegrals.UnimodGenus
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.Bridge

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unimodular_genus_unique : PI.UnimodGenus :=
  PI.UG.W.unimodGenus_of PI.UG.W.unimodLocal PI.UG.W.isomLocStd
