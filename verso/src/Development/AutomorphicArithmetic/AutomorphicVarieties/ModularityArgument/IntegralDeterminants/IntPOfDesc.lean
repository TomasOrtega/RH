import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.SlopeAll
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.QuadLift

namespace UpperTheory.V.Z.Int

/- English proof (translation)
The claim follows from `intP UpperTheory.ConvolutionTheory.Sph.quadLift hD`.
-/
theorem intP_of_desc (hD : GlobalTheory.Cong.DescOffT) : UpperTheory.V.Br.IntP := intP UpperTheory.ConvolutionTheory.Sph.quadLift hD

/- English proof (translation)
The claim follows from `intK UpperTheory.ConvolutionTheory.Sph.quadLift hD`.
-/
theorem intK_of_desc (hD : GlobalTheory.Cong.DescOffT) : UpperTheory.V.Af.IntK := intK UpperTheory.ConvolutionTheory.Sph.quadLift hD

end UpperTheory.V.Z.Int
