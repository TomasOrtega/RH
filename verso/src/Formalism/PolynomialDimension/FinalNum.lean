import Formalism.PolynomialDimension.MultinomialDepth.SecondParameterSizeBoundsHolds
import Formalism.PolynomialDimension.MultinomialDepth.SecondParameterSlackBoundsHolds
import Formalism.PolynomialDimension.MultinomialDepth.FrameMultinomialBoundHolds
import Formalism.PolynomialDimension.MultinomialDepth.ParamsI
import Formalism.PolynomialDimension.MultinomialDepth.IntervalCleanDepthBound

namespace Formalism.CountingSumsFrames.Top

/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.secondParameterSizeBounds_holds`.
-/
theorem paramsII0 : Formalism.CountingSumsFrames.ParamsII0 := Formalism.CountingSumsFrames.secondParameterSizeBounds_holds
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.secondParameterSlackBounds_holds`.
-/
theorem paramsII5 : Formalism.CountingSumsFrames.ParamsII5 := Formalism.CountingSumsFrames.secondParameterSlackBounds_holds

/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.interval_kappa_bound`.
-/
theorem kapI : Formalism.CountingSumsFrames.KapI := Formalism.CountingSumsFrames.interval_kappa_bound

end Formalism.CountingSumsFrames.Top
