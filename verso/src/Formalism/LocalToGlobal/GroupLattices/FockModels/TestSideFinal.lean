import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSide
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FormCoreSK

namespace Formalism.L2.G.Model

/- English proof (translation)
The claim follows from `TS.Top.formCoreSK`.
-/
theorem formCore : FormCore := TS.Top.formCoreSK

/- English proof (translation)
The claim follows from `testSide_of_core formCore`.
-/
theorem testSide : Formalism.MainNotions.G.TestSide := testSide_of_core formCore

end Formalism.L2.G.Model
