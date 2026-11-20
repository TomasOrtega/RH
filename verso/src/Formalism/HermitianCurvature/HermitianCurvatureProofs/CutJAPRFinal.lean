import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRRest
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecomp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPWordAsm

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

/- English proof (translation)
The claim follows from `polyRadialS_of CP.radial_decomposition_holds CP.word_polynomial_vector_holds`.
-/
theorem polynomial_radial_holds : PolyRadialS := polyRadialS_of CP.radial_decomposition_holds CP.word_polynomial_vector_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
