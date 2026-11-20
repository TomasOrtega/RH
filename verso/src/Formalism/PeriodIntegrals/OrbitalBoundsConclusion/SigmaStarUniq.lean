import Mathlib
import Formalism.PeriodIntegrals.SigmaStarUniq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AreaLat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.SigmaStarUniqOf

/- English proof (translation)
The claim follows from `PI.SSU.sigmaStarUniq_of area_lattice_formula`.
-/
theorem sigma_star_unique : PI.SigmaStarUniq := PI.SSU.sigmaStarUniq_of area_lattice_formula
