import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitDetRoot

namespace Formalism.L2.Th1.H

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kappaExists : KappaExists := unit_det_root_of_unity

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem quadraticSemicharacters_of_localStandard (hL : LocalStandard) : quadraticSemicharacterIdentityReformulated := quadraticSemicharacters_of_fact hL kappaExists

end Formalism.L2.Th1.H
