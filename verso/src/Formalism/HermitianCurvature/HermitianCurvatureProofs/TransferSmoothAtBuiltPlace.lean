import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfCapJoints
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SinglePairFinsuppEqIff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem chart_equations_holds : ChartEqs :=
  chartEqs_of_capJoints capelli_words_holds right_capelli_words_holds left_capelli_words_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem model_place_built_holds : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 := modelPlaceBuilt2_of_chartEqs chart_equations_holds

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
