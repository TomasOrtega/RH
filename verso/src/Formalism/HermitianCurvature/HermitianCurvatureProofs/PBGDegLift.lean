import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightAverageSmoothComm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.PBG.degLift_of_parts Formalism.FourierDecayAlt.P.left_fubini_normalized_tower Formalism.FourierDecayAlt.P.PBG.right_average_smooth_comm`.
-/
theorem Formalism.FourierDecayAlt.P.degree_of_lift_pairing : Formalism.FourierDecayAlt.KB.DegLift :=
  Formalism.FourierDecayAlt.P.PBG.degLift_of_parts Formalism.FourierDecayAlt.P.left_fubini_normalized_tower Formalism.FourierDecayAlt.P.PBG.right_average_smooth_comm
