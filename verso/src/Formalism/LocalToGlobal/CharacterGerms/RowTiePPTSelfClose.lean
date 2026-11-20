import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTClose
import Formalism.LocalToGlobal.CharacterGerms.RowTiePStartSelf

namespace Formalism.L2.FormalSeriesBounds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ptSelf_of_lieSelf (h : ProjLieSelfSt) : PTSelfSt := ptSelf_of_start2 (allStartSelf_of h)

end Formalism.L2.FormalSeriesBounds
