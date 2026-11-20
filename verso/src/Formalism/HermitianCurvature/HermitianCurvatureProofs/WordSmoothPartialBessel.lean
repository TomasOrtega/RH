import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordSmoothPartialBesselInduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProperDomP

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem word_smooth_partial_bessel : CutHB.WordSmooth := PartialBesselWordSmoothness.wordSmooth_of proper_left_variables_domain

end Formalism.FourierDecayAlt.P
