import Formalism.SharpRestriction.GlobalSchurBounds.SlopeMaxOpenOfHookTwoLeV
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.StdSlopeLow
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HookBound

namespace Formalism.MainNotions.flipTwoThree

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stdSlopeLow_holds : StdSlopeLow := standard_slope_lower

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hookBound_holds : HookBound := hook_length_bound

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lower_slope_of_column_slope (D : Formalism.BasicNotions.D7) (hC : ColSlopeEq D) : SlopeLowerOpenPart D := slopeLowerOpen_of_std_hook stdSlopeLow_holds hookBound_holds D hC

end Formalism.MainNotions.flipTwoThree
