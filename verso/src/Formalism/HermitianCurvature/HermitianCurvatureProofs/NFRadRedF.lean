import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalReductionOperator

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `representation_smooth_of_log local_logarithm_unitary`.
-/
theorem representation_smooth : NFRadRedS.RepSmooth := representation_smooth_of_log local_logarithm_unitary

/- English proof (translation)
The claim follows from `radical_surjective_of_parts local_smooth_section representation_smooth`.
-/
theorem radical_reduction_surjective : Formalism.FourierDecayAlt.NF.RadRedSurj :=
  radical_surjective_of_parts local_smooth_section representation_smooth

end Formalism.FourierDecayAlt.P
