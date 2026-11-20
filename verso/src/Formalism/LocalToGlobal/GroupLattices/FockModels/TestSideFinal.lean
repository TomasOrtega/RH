import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSide
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FormCoreSK

namespace Formalism.L2.G.Model

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem formCore : FormCore := TS.Top.formCoreSK

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem testSide : Formalism.MainNotions.G.TestSide := testSide_of_core formCore

end Formalism.L2.G.Model
