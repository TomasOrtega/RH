import Mathlib
import Formalism.PeriodIntegrals.MinkowskiQ
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Minkowski
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiTorsionFree.Lattice

/- English proof (translation)
The claim follows from `PI.MkQ.minkowskiBoundQ`.
-/
theorem minkowski_bound_rat : PI.MinkowskiBoundQ := PI.MkQ.minkowskiBoundQ
