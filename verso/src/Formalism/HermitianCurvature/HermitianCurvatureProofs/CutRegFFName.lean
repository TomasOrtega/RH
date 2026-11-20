import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFF

namespace Formalism.FourierDecayAlt.P.CutMP

abbrev JfSmoothBuilt : Prop := JfSmoothDS

/- English proof (translation)
The claim follows from `modelPlaceBuilt2_of_3 hJ h3`.
-/
theorem modelPlaceBuilt2_of_3' (hJ : JfSmoothBuilt) (h3 : ModelPlaceBuilt3) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_3 hJ h3

end Formalism.FourierDecayAlt.P.CutMP
