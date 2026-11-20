import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.WeilBound.NonsplitUniqueness.Places

/- English proof (translation)
The claim follows from `PositivityTheory.tft.places_holds`.
-/
theorem UpperTheory.ConvolutionTheory.T.places :
    UpperTheory.ConvolutionTheory.T.Places := PositivityTheory.tft.places_holds
