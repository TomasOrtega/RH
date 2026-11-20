import Mathlib
import Formalism.PeriodIntegrals.KerLat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PeriodPairIndependence.IndepOfImNe

/- English proof (translation)
The claim follows from `PI.KerLat.PerPairProof.perPair`.
-/
theorem exists_periodPairOfIdeal : PI.KerLat.PerPair := PI.KerLat.PerPairProof.perPair
