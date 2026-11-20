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
The claim follows from `logDerivBoundInRegionOfBounds zeroFreeRegion logDerivBoundRightHalfPlane growthBound zetaInvBound_statement logDerivBoundedHeight landauLocal`.
-/
theorem logDerivRegion : LogDerivRegion :=
  logDerivBoundInRegionOfBounds zeroFreeRegion logDerivBoundRightHalfPlane growthBound zetaInvBound_statement
    logDerivBoundedHeight landauLocal

/- English proof (translation)
The claim follows from `rectangleShiftOfResidue rectangle_double_pole laurentExpansionAtOne`.
-/
theorem rectShift : RectShift := rectangleShiftOfResidue rectangle_double_pole laurentExpansionAtOne

/- English proof (translation)
The claim follows from `zetaPrimeSumErrorBoundOfBounds zeroFreeRegion logDerivRegion logDerivBoundRightHalfPlane perron_formula rectShift`.
-/
theorem gzPNT : GzPNT :=
  zetaPrimeSumErrorBoundOfBounds zeroFreeRegion logDerivRegion logDerivBoundRightHalfPlane perron_formula rectShift

end Formalism.ZF
