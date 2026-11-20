import Formalism.FormalDegreeBessel.FormalDegreeRatio.IOLeft
import Formalism.FormalDegreeBessel.FormalDegreeRatio.IOCentral
import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated

namespace Formalism.QuantumDeterminants

/- English proof (translation)
The claim follows from `gl_relation_adjoint_holds`.
-/
theorem glRelAd : GlRelAd := gl_relation_adjoint_holds
/- English proof (translation)
The claim follows from `capelli_central_holds`.
-/
theorem capCentral : CapCentral := capelli_central_holds
/- English proof (translation)
The claim follows from `quantum_minor_left_holds`.
-/
theorem qMinorLeft : QMinorLeft := quantum_minor_left_holds
/- English proof (translation)
The claim follows from `capelli_left_holds`.
-/
theorem capLeft : CapLeft := capelli_left_holds
/- English proof (translation)
The claim follows from `capelli_highest_weight_holds`.
-/
theorem capHW : CapHW := capelli_highest_weight_holds
/- English proof (translation)
The claim follows from `capelli_comatrix_holds`.
-/
theorem capComatrix : CapComatrix := capelli_comatrix_holds
/- English proof (translation)
The claim follows from `conjugated_generator_transport`.
-/
theorem eabHTransport : EabHTransport := conjugated_generator_transport
/- English proof (translation)
The claim follows from `conjugated_generator_gl_relation`.
-/
theorem eabHGl : EabHGl := conjugated_generator_gl_relation
/- English proof (translation)
The claim follows from `capelli_central_conjugated`.
-/
theorem capCentralH : CapCentralH := capelli_central_conjugated
/- English proof (translation)
The claim follows from `capelli_left_conjugated`.
-/
theorem capLeftH : CapLeftH := capelli_left_conjugated
/- English proof (translation)
The claim follows from `capelli_highest_weight_conjugated`.
-/
theorem capHWH : CapHWH := capelli_highest_weight_conjugated

end Formalism.QuantumDeterminants
