import Mathlib
import Formalism.PeriodIntegrals.SigmaStarUniq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AreaLat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.SigmaStarUniqOf

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigma_star_unique : PI.SigmaStarUniq := PI.SSU.sigmaStarUniq_of area_lattice_formula
