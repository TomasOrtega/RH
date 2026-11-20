import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.FinalKappa
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnimodLocStd

namespace Formalism.L2.Th1.H

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem localStandard : LocalStandard := unimodular_local_standard

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem quadraticSemicharacter_identity_reformulated : quadraticSemicharacterIdentityReformulated := quadraticSemicharacters_of_fact localStandard kappaExists

end Formalism.L2.Th1.H
