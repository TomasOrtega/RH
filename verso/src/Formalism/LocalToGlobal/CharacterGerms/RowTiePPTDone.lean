import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTEig
import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEig2

namespace Formalism.L2.FormalSeriesBounds

/- English proof (translation)
The claim follows from `ptSelf_of_eig RowTiePKey.keyEig_holds`.
-/
theorem ptSelf_holds : PTSelfSt := ptSelf_of_eig RowTiePKey.keyEig_holds

end Formalism.L2.FormalSeriesBounds
