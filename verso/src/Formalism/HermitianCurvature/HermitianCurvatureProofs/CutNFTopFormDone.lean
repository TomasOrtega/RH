import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDMAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_TypeNormMeas_Proof
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DominatedL2TruncationBoundHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopForm

namespace Formalism.FourierDecayAlt.P.CutBP

/- English proof (translation)
The claim follows from `TDM.topDMeasCpt_of_typeNormMeas type_norm_measurability_holds`.
-/
theorem top_domination_measurable_compact : TopDMeasCpt := TDM.topDMeasCpt_of_typeNormMeas type_norm_measurability_holds

/- English proof (translation)
The claim follows from `nFTopFormAll_of top_domination_measurable_compact (nfApxDomAll_of_ptw hP)`.
-/
theorem nFTopFormAll_of_ptw (hP : NFDomPtw) : NFTopFormAll :=
  nFTopFormAll_of top_domination_measurable_compact (nfApxDomAll_of_ptw hP)

end Formalism.FourierDecayAlt.P.CutBP
