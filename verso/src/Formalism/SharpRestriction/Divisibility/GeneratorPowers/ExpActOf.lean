import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpOfPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActPf

set_option autoImplicit false

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

/- English proof (translation)
The claim follows from `expActOf_of_eig hE`.
-/
theorem expActOf_of (hE : LinEigSt) : ExpActOfSt := expActOf_of_eig hE

end Formalism.MainNotions.ModuliIntegralCharts.H1
