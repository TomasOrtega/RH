import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneEightOfDifferent
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.BasicNotions

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem diffK_holds (D : D7) : DiffK D := HK.diffK_holds D.host

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem normK_holds (D : D7) : NormK D := HK.normK_holds D.host

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemma_one_eight_holds (D : D7) : Conclusion8 D := lemma_one_eight_of_different D (diffK_holds D) (normK_holds D)

end Formalism.MainNotions.UnusedSlot33
