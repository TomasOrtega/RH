import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnFoldRev
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnAdmLen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBesselFold
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCVInCC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.L2BoundAtBuiltPlaceHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame

namespace Formalism.FourierDecayAlt.P.CutMP

/- English proof (translation)
The claim follows from `En.besselFoldBuilt_of En.coefficient_vector_in_L2_class`.
-/
theorem En.bessel_folding_at_built_place : En.BesselFoldBuilt := En.besselFoldBuilt_of En.coefficient_vector_in_L2_class

/- English proof (translation)
The claim follows from `En.energyTr_of_parts En.folding_reversal_holds En.admissible_length_holds En.bessel_folding_at_built_place En.L2_bound_at_built_place_holds h`.
-/
theorem energyTr_of_betaFrame (h : En.BetaFrame) : EnergyTr :=
  En.energyTr_of_parts En.folding_reversal_holds En.admissible_length_holds En.bessel_folding_at_built_place En.L2_bound_at_built_place_holds h

/- English proof (translation)
The claim follows from `energyTr_of_betaFrame En.beta_frame_identity_holds`.
-/
theorem energy_trace_identity_holds : EnergyTr := energyTr_of_betaFrame En.beta_frame_identity_holds

end Formalism.FourierDecayAlt.P.CutMP
