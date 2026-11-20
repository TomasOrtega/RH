import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDMSE
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDMVV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDMDop

namespace Formalism.FourierDecayAlt.P.CutBP.TDM

/- English proof (translation)
The claim follows from `topDMeasCpt_of_parts h vector_positive_cone diff_operator_in_class_CC scalar_point_measurability_holds empty_list_measurability_holds`.
-/
theorem topDMeasCpt_of_typeNormMeas (h : TypeNormMeas) : TopDMeasCpt :=
  topDMeasCpt_of_parts h vector_positive_cone diff_operator_in_class_CC scalar_point_measurability_holds empty_list_measurability_holds

end Formalism.FourierDecayAlt.P.CutBP.TDM
