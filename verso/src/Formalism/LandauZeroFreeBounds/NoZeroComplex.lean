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

/- English proof (translation)
The claim follows from `localZeroSumBoundOfBounds localZeroExpansionWithMultiplicity lfunction_polynomial_growth inverseBound`.
-/
theorem localZeros : LocalZeros :=
  localZeroSumBoundOfBounds localZeroExpansionWithMultiplicity lfunction_polynomial_growth inverseBound

/- English proof (translation)
The claim follows from `zeroFreeNonRealCharOfBounds localZeros l_log_deriv_right negLogDerivPositivity`.
-/
theorem noZeroComplex : NoZeroComplex :=
  zeroFreeNonRealCharOfBounds localZeros l_log_deriv_right negLogDerivPositivity

/- English proof (translation)
The claim follows from `realCharZeroFreeLargeHeightOfBounds localZeros l_log_deriv_right negLogDerivPositivity trivial_log_deriv_bound`.
-/
theorem realLargeT : RealLargeT :=
  realCharZeroFreeLargeHeightOfBounds localZeros l_log_deriv_right negLogDerivPositivity trivial_log_deriv_bound

/- English proof (translation)
The claim follows from `realCharZeroSmallHeightOfBounds localZeros l_log_deriv_right negLogDerivPositivity realCharConj`.
-/
theorem realSmallT : RealSmallT :=
  realCharZeroSmallHeightOfBounds localZeros l_log_deriv_right negLogDerivPositivity realCharConj

/- English proof (translation)
The claim follows from `twoRealCharNoCommonZeroOfBounds localZeros l_log_deriv_right negLogDerivPositivity`.
-/
theorem twoReal : TwoReal :=
  twoRealCharNoCommonZeroOfBounds localZeros l_log_deriv_right negLogDerivPositivity

/- English proof (translation)
The claim follows from `zeroFreeRegionExceptionalZeroOfBounds Formalism.ZF.zeroFreeRegion trivialCharZerosOfZeta noZeroComplex realLargeT realSmallT twoReal`.
-/
theorem zFRDirichlet : ZFRDirichlet :=
  zeroFreeRegionExceptionalZeroOfBounds Formalism.ZF.zeroFreeRegion trivialCharZerosOfZeta noZeroComplex realLargeT realSmallT twoReal

end Formalism.ZeroFreeDirichlet
