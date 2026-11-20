import Formalism.LocalToGlobal.CharacterGerms.RowTieCartTop
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm

namespace Formalism.L2.FormalSeriesBounds

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ Y` and use `germI_holds Y`.
-/
theorem germIAll_holds : GermIAllSt := fun _ _ _ _ _ _ _ _ Y => germI_holds Y

end Formalism.L2.FormalSeriesBounds
