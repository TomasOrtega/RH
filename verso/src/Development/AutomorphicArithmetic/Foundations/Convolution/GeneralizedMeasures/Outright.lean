import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.GmOfBcfl
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.BcflUnit

/- English proof (translation)
The claim follows from `UpperTheory.ConvolutionTheory.GM.gm_of_bcfl PositivityTheory.Rg.Tf.Loc.bcflUnit`.
-/
theorem UpperTheory.ConvolutionTheory.GM.gm : UpperTheory.ConvolutionTheory.GM.GM := UpperTheory.ConvolutionTheory.GM.gm_of_bcfl PositivityTheory.Rg.Tf.Loc.bcflUnit
