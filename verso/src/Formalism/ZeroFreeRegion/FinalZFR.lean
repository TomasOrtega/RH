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

/- English proof (authored)
Combine the factorization of zeros in the inner disk with the logarithmic derivative bound for the zero-free remainder. The local expansion theorem gives the finite zero terms and the resulting remainder estimate.
-/
theorem landauLocal : LandauLocal := localZeroExpansionOfFactorization zeroFactorization logDerivBoundOnBall

/- English proof (authored)
Apply the classical zero-free region argument using the three-four-one positivity inequality, the right-half-plane derivative bound, and the zeta growth and inverse bounds. The local zero expansion controls large heights, and the bounded-height result supplies the remaining range.
-/
theorem zeroFreeRegion : ZeroFreeRegion :=
  classicalZeroFreeRegionOfBounds mertensInequality logDerivBoundRightHalfPlane growthBound zetaInvBound_statement
    zeroFreeBoundedHeight landauLocal

end Formalism.ZF
