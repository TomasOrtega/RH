import Formalism.HermitianCurvature.HermitianCurvatureProofs.RhoAntitoneOfInterlacing
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivedCoefficientIntegrable

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eigenvalue_interlacing : Formalism.FourierDecayAlt.C7.LemmaEInterlacing :=
  interlacing_of_parts le_E_proof roots_outside_jointly

end Formalism.FourierDecayAlt.P
