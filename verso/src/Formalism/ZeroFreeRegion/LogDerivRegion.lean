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

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem logDerivRegion : LogDerivRegion :=
  logDerivBoundInRegionOfBounds zeroFreeRegion logDerivBoundRightHalfPlane growthBound zetaInvBound_statement
    logDerivBoundedHeight landauLocal

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rectShift : RectShift := rectangleShiftOfResidue rectangle_double_pole laurentExpansionAtOne

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gzPNT : GzPNT :=
  zetaPrimeSumErrorBoundOfBounds zeroFreeRegion logDerivRegion logDerivBoundRightHalfPlane perron_formula rectShift

end Formalism.ZF
