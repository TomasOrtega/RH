import Formalism.FormalDegreeBessel.FormalDegreeRatio.IOLeft
import Formalism.FormalDegreeBessel.FormalDegreeRatio.IOCentral
import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated

namespace Formalism.QuantumDeterminants

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem glRelAd : GlRelAd := gl_relation_adjoint_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem capCentral : CapCentral := capelli_central_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem qMinorLeft : QMinorLeft := quantum_minor_left_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem capLeft : CapLeft := capelli_left_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem capHW : CapHW := capelli_highest_weight_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem capComatrix : CapComatrix := capelli_comatrix_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eabHTransport : EabHTransport := conjugated_generator_transport
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eabHGl : EabHGl := conjugated_generator_gl_relation
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem capCentralH : CapCentralH := capelli_central_conjugated
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem capLeftH : CapLeftH := capelli_left_conjugated
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem capHWH : CapHWH := capelli_highest_weight_conjugated

end Formalism.QuantumDeterminants
