import Mathlib
import Formalism.PeriodIntegrals.SqPair
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocCartanPair
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SqPairLocalOf

/- English proof (translation)
The claim follows from `PI.SqPairLocal.sqPairLocal_of local_cartan_pair`.
-/
theorem square_pair_local : PI.SqPair.PLocalAll := PI.SqPairLocal.sqPairLocal_of local_cartan_pair
