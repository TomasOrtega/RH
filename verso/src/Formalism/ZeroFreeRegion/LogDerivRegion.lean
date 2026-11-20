import Formalism.ZeroFreeRegion.FinalZFR
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.SmallHeightLogDeriv
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivRegionOf
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Perron
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RectDoublePole
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LaurentAtOne
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RectShiftOf
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.GzPNTOf

noncomputable section

namespace Formalism.ZF

/- English proof (authored)
Apply the logarithmic derivative region theorem with the zeta zero-free region, the right-half-plane, growth, and inverse estimates, and the local zero expansion. The bounded-height logarithmic derivative estimate covers the small-height part of the conclusion.
-/
theorem logDerivRegion : LogDerivRegion :=
  logDerivBoundInRegionOfBounds zeroFreeRegion logDerivBoundRightHalfPlane growthBound zetaInvBound_statement
    logDerivBoundedHeight landauLocal

/- English proof (authored)
Use the rectangle formula for a function with a double pole. The Laurent expansion at one gives its two principal coefficients, so the specified contour shift follows.
-/
theorem rectShift : RectShift := rectangleShiftOfResidue rectangle_double_pole laurentExpansionAtOne

/- English proof (authored)
Combine the zero-free region, logarithmic derivative bounds inside it and to the right of one, and the Perron formula with its rectangle shift. The prime-sum error theorem then gives the smoothed zeta prime-number-theorem estimate.
-/
theorem gzPNT : GzPNT :=
  zetaPrimeSumErrorBoundOfBounds zeroFreeRegion logDerivRegion logDerivBoundRightHalfPlane perron_formula rectShift

end Formalism.ZF
