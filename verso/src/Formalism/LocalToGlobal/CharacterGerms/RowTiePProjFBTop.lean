import Formalism.LocalToGlobal.CharacterGerms.RowTiePLSmallMain

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePProj

/- English proof (translation)
The claim follows from `projFB_of RowTiePLSmall.lSmall_holds hLie`.
-/
theorem projFB_of_lie (hLie : ProjLieSt) : ProjFBSt := projFB_of RowTiePLSmall.lSmall_holds hLie

end RowTiePProj

end Formalism.L2.FormalSeriesBounds
