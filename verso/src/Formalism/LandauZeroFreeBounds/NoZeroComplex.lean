import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LocalZeroExpansionWithMultiplicity
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Positivity
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TrivLogDeriv
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TrivReal
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LocalZerosOf
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.NoZeroComplexOf
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RealLargeTOf
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RealSmallTOf
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TwoRealOf
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZFRDirichletOf
import Formalism.ZeroFreeRegion.FinalZFR

namespace Formalism.ZeroFreeDirichlet

/- English proof (authored)
Apply the local-zero estimate with the multiplicity expansion, polynomial growth bound, and reciprocal L-function bound. These are its three required inputs.
-/
theorem localZeros : LocalZeros :=
  localZeroSumBoundOfBounds localZeroExpansionWithMultiplicity lfunction_polynomial_growth inverseBound

/- English proof (authored)
Apply the nonreal-character zero exclusion with the local zero expansion, the right-half-plane derivative estimate, and the three-four-one positivity inequalities.
-/
theorem noZeroComplex : NoZeroComplex :=
  zeroFreeNonRealCharOfBounds localZeros l_log_deriv_right negLogDerivPositivity

/- English proof (authored)
Use the large-height real-character exclusion with the local zero expansion, derivative estimate, positivity, and the special bound for the principal logarithmic derivative at double height.
-/
theorem realLargeT : RealLargeT :=
  realCharZeroFreeLargeHeightOfBounds localZeros l_log_deriv_right negLogDerivPositivity trivial_log_deriv_bound

/- English proof (authored)
Use the small-height real-character theorem with the local zero expansion, right-half-plane bound, and positivity. Conjugation of real-character L-functions supplies its final hypothesis and makes any surviving zero real.
-/
theorem realSmallT : RealSmallT :=
  realCharZeroSmallHeightOfBounds localZeros l_log_deriv_right negLogDerivPositivity realCharConj

/- English proof (authored)
The two-character exclusion follows from the local zero estimates, the right-half-plane logarithmic derivative bound, and the nonnegative four-character combination.
-/
theorem twoReal : TwoReal :=
  twoRealCharNoCommonZeroOfBounds localZeros l_log_deriv_right negLogDerivPositivity

/- English proof (authored)
Combine the zeta zero-free region and the reduction for principal characters with the exclusions for nonreal characters and for real characters of large height. The small-height theorem gives reality, simplicity, and uniqueness for a fixed character, and the two-character exclusion gives uniqueness across characters.
-/
theorem zFRDirichlet : ZFRDirichlet :=
  zeroFreeRegionExceptionalZeroOfBounds Formalism.ZF.zeroFreeRegion trivialCharZerosOfZeta noZeroComplex realLargeT realSmallT twoReal

end Formalism.ZeroFreeDirichlet
