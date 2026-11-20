import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.FinalKappa
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnimodLocStd

namespace Formalism.L2.Th1.H

/- English proof (translation)
The claim follows from `unimodular_local_standard`.
-/
theorem localStandard : LocalStandard := unimodular_local_standard

/- English proof (translation)
The claim follows from `quadraticSemicharacters_of_fact localStandard kappaExists`.
-/
theorem quadraticSemicharacter_identity_reformulated : quadraticSemicharacterIdentityReformulated := quadraticSemicharacters_of_fact localStandard kappaExists

end Formalism.L2.Th1.H
