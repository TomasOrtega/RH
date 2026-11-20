import Mathlib
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceMinima

namespace GlobalTheory

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem transferenceCover_holds : PI.TransferenceCover :=
  PI.Tr.transferenceCover_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall

end GlobalTheory
