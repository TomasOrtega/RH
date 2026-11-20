import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TCGlue
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestSegCoreOfNum
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TCXNum

namespace Formalism.MainNotions.ColumnSystems.Pf

/- English proof (translation)
The claim follows from `restTCore_of_seg (restSegCore_of_num restNumCore)`.
-/
theorem restTCore : RestTCore := restTCore_of_seg (restSegCore_of_num restNumCore)

end Formalism.MainNotions.ColumnSystems.Pf
