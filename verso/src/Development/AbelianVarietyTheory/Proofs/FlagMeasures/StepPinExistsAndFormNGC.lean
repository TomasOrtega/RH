import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRelHolds

namespace GlobalTheory

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem stepPinExists_and_formNGC :
    Formalism.L2.SG.NGAnalytic.StepPinExists ∧ Formalism.L2.SG.NGVanish.FormNGC :=
  ⟨Formalism.L2.SG.NGPin.stepPinExists, Formalism.L2.SG.Pf.formNGC_holds⟩

end GlobalTheory
