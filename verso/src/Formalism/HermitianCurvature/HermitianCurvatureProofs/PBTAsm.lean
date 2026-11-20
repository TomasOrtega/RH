import Formalism.HermitianCurvature.HermitianCurvatureProofs.SupportPhiZeroSubset
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsMeasurableSection
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AutomorphicInSphericalLevel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FibreIntegralCells
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DensityConstantOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem phi_zero_hermitian_curvature : Formalism.FourierDecayAlt.KB.PhiZero :=
  phi_zero_of_parts pbi_sectionExists_proof fibre_integral_smooth fibre_integral_cells

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem density_constant : Formalism.FourierDecayAlt.KB.DensC :=
  pb_densC_of phi_zero_hermitian_curvature vector_vanishes_big_cell

end Formalism.FourierDecayAlt.P
