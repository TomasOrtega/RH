import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivBound
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZeroFactor
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LandauLocalOf
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ThreeFourOne
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivRight
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaGrowth
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaInvBound
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.SmallHeight
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZeroFreeOf

noncomputable section

namespace Formalism.ZF

/- English proof (translation)
The claim follows from `localZeroExpansionOfFactorization zeroFactorization logDerivBoundOnBall`.
-/
theorem landauLocal : LandauLocal := localZeroExpansionOfFactorization zeroFactorization logDerivBoundOnBall

/- English proof (translation)
The claim follows from `classicalZeroFreeRegionOfBounds mertensInequality logDerivBoundRightHalfPlane growthBound zetaInvBound_statement zeroFreeBoundedHeight landauLocal`.
-/
theorem zeroFreeRegion : ZeroFreeRegion :=
  classicalZeroFreeRegionOfBounds mertensInequality logDerivBoundRightHalfPlane growthBound zetaInvBound_statement
    zeroFreeBoundedHeight landauLocal

end Formalism.ZF
