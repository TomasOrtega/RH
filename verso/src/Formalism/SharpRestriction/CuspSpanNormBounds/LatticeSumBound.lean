import Formalism.SharpRestriction.CuspSpanNormBounds.KTwoMinorIntegrality
import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedLatticeSum

noncomputable section

namespace Formalism.MainNotions.LatticeSumConvergence

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem LatSum_holds : Formalism.MainNotions.KTwoMinorIntegrality.LatSum :=
  fun ι _ P R hR hsep => Formalism.MainNotions.WeightedLatticeSum.latSum ι P R hR hsep

end Formalism.MainNotions.LatticeSumConvergence

end
