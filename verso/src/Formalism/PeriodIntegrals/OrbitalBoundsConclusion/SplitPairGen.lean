import Mathlib
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SqPairGlue
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SqPairLocal

/- English proof (translation)
The claim follows from `square_pair_glue square_pair_local`.
-/
theorem split_pair_generation : Formalism.L2.PairingIndexBounds.Eq.SqG.SplitPairGen := square_pair_glue square_pair_local
