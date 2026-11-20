import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTEx
import Formalism.LocalToGlobal.CharacterGerms.RowTiePOAct

namespace Formalism.L2.FormalSeriesBounds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ptFB_of_start3 (hS : AllStartFBSt) (hStab : HStabFBSt) : PTFBSt :=
  ptFB_of_start2 hS OAct.oActTySt_holds hStab

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cartFB_of_start (hS : AllStartFBSt) (hStab : HStabFBSt) : CartFBSt :=
  cartesian_of_germs (ptFB_of_start3 hS hStab) germIAll_holds hStab

end Formalism.L2.FormalSeriesBounds
