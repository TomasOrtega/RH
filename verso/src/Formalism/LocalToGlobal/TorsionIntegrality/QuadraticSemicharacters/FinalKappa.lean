import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitDetRoot

namespace Formalism.L2.Th1.H

/- English proof (translation)
The claim follows from `unit_det_root_of_unity`.
-/
theorem kappaExists : KappaExists := unit_det_root_of_unity

/- English proof (translation)
The claim follows from `quadraticSemicharacters_of_fact hL kappaExists`.
-/
theorem quadraticSemicharacters_of_localStandard (hL : LocalStandard) : quadraticSemicharacterIdentityReformulated := quadraticSemicharacters_of_fact hL kappaExists

end Formalism.L2.Th1.H
