import Formalism.SharpRestriction.CuspSpanNormBounds.KTwoMinorIntegrality
import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedLatticeSum

noncomputable section

namespace Formalism.MainNotions.LatticeSumConvergence

/- English proof (translation)
Introduce `ι _ P R hR hsep` and use `Formalism.MainNotions.WeightedLatticeSum.latSum ι P R hR hsep`.
-/
theorem LatSum_holds : Formalism.MainNotions.KTwoMinorIntegrality.LatSum :=
  fun ι _ P R hR hsep => Formalism.MainNotions.WeightedLatticeSum.latSum ι P R hR hsep

end Formalism.MainNotions.LatticeSumConvergence

end
