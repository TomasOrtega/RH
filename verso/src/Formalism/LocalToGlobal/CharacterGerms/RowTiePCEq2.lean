import Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqEx

namespace Formalism.L2.FormalSeriesBounds

/- English proof (translation)
The claim follows from `cEqFB_of cEqSum_holds (cEqDer_of (fun _ _ _ _ _ _ _ _ Y => exDer_holds Y) (fun _ _ _ _ _ _ _ _ Y => germIIM_holds Y))`.
-/
theorem cEqFB_holds : CEqFBSt :=
  cEqFB_of cEqSum_holds
    (cEqDer_of (fun _ _ _ _ _ _ _ _ Y => exDer_holds Y) (fun _ _ _ _ _ _ _ _ Y => germIIM_holds Y))

end Formalism.L2.FormalSeriesBounds
