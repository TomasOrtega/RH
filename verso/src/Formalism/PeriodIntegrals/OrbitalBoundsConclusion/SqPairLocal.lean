import Mathlib
import Formalism.PeriodIntegrals.SqPair
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocCartanPair
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SqPairLocalOf

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem square_pair_local : PI.SqPair.PLocalAll := PI.SqPairLocal.sqPairLocal_of local_cartan_pair
