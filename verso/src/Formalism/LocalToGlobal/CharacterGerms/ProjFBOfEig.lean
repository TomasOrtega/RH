import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyTop
import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyRes2

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

/- English proof (translation)
The claim follows from `projFB_of_eig_res hE RowTiePKeyRes.keyRes_holds`.
-/
theorem projFB_of_eig (hE : KeyEigSt) : ProjFBSt := projFB_of_eig_res hE RowTiePKeyRes.keyRes_holds

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
