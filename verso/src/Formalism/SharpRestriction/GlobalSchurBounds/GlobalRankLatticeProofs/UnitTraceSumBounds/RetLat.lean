import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.SigmaStarUniq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AreaLat
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransInvLat
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SigmaStarUniq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiscrNe
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SigmaStarEx

namespace Formalism.MainNotions.Ext

/- English proof (translation)
The claim follows from `area_lattice_formula`.
-/
theorem areaLat_holds : AreaLat := area_lattice_formula

/- English proof (translation)
The claim follows from `translation_invariant_lattice`.
-/
theorem transInvLat_holds : TransInvLat := translation_invariant_lattice

/- English proof (translation)
The claim follows from `sigma_star_unique`.
-/
theorem sigmaStarUniq_holds : SigmaStarUniq := sigma_star_unique

/- English proof (translation)
The claim follows from `discrNe'`.
-/
theorem discrNe_holds : DiscrNe := discrNe'

/- English proof (translation)
The claim follows from `sigma_star_exists`.
-/
theorem sigmaStarEx_holds : SigmaStarEx := sigma_star_exists

end Formalism.MainNotions.Ext
