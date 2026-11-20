import Mathlib
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceMinima

namespace GlobalTheory

/- English proof (translation)
The claim follows from `PI.Tr.transferenceCover_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall`.
-/
theorem transferenceCover_holds : PI.TransferenceCover :=
  PI.Tr.transferenceCover_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall

end GlobalTheory
