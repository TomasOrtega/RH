import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTFinal
import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTSelfEx
import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActSelf
import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStab
import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStabSelf

namespace Formalism.L2.FormalSeriesBounds

/- English proof (translation)
The claim follows from `ptFB_of_proj hP hStabFB`.
-/
theorem ptFB_of_proj2 (hP : ProjFBSt) : PTFBSt := ptFB_of_proj hP hStabFB

/- English proof (translation)
The claim follows from `cartFB_of_proj hP hStabFB`.
-/
theorem cartFB_of_proj2 (hP : ProjFBSt) : CartFBSt := cartFB_of_proj hP hStabFB

/- English proof (translation)
The claim follows from `ptFB_of_lie hLie hStabFB`.
-/
theorem typical_curves_of_lie (hLie : RowTiePProj.ProjLieSt) : PTFBSt := ptFB_of_lie hLie hStabFB

/- English proof (translation)
The claim follows from `ptSelf_of_start hS OActSelf.oActSelf_holds hStabSelf_holds`.
-/
theorem ptSelf_of_start2 (hS : AllStartSelfSt) : PTSelfSt :=
  ptSelf_of_start hS OActSelf.oActSelf_holds hStabSelf_holds

/- English proof (translation)
The claim follows from `ptAvgSelf_of OActSelf.oActSelf_holds limSelf_holds`.
-/
theorem ptAvgSelf_holds : PTAvgSelfSt := ptAvgSelf_of OActSelf.oActSelf_holds limSelf_holds

end Formalism.L2.FormalSeriesBounds
