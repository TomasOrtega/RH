import Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqEx

namespace Formalism.L2.FormalSeriesBounds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cEqFB_holds : CEqFBSt :=
  cEqFB_of cEqSum_holds
    (cEqDer_of (fun _ _ _ _ _ _ _ _ Y => exDer_holds Y) (fun _ _ _ _ _ _ _ _ Y => germIIM_holds Y))

end Formalism.L2.FormalSeriesBounds
