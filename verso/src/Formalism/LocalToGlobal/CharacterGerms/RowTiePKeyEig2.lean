import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEigD
import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyTeich2
import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyJoint

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

/- English proof (translation)
The claim follows from `RowTiePKeyEig.keyEig_of RowTiePKeyTeich.teich_holds jointEig_holds`.
-/
theorem keyEig_holds : KeyEigSt := RowTiePKeyEig.keyEig_of RowTiePKeyTeich.teich_holds jointEig_holds

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
