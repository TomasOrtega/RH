import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.InvInv
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.InvInt
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.HomRelationHolds
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.SchurTraceOfHomInv
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.TypeInt
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.LatticeBasisPolynomial
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.OrthogonalIsomorphismHolds
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.CommProjectionHolds
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.PolLeISupIsoW
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.Discharge

namespace Formalism.InvariantFactorPaths.PW.Top

/- English proof (translation)
The claim follows from `invariant_inverse_holds`.
-/
theorem invInv : InvInv := invariant_inverse_holds
/- English proof (translation)
The claim follows from `invariant_natural_holds`.
-/
theorem invNat : InvNat := invariant_natural_holds
/- English proof (translation)
The claim follows from `invariant_integral_holds`.
-/
theorem invInt : InvInt := invariant_integral_holds
/- English proof (translation)
The claim follows from `hom_relation_holds`.
-/
theorem homRel : HomRel := hom_relation_holds
/- English proof (translation)
The claim follows from `hom_divided_holds`.
-/
theorem homDiv : HomDiv := hom_divided_holds
/- English proof (translation)
The claim follows from `hom_trace_holds`.
-/
theorem homTrace : HomTrace := hom_trace_holds
/- English proof (translation)
The claim follows from `homInv_of invInv`.
-/
theorem homInv : HomInv := homInv_of invInv
/- English proof (translation)
The claim follows from `schurTrace_of invInv`.
-/
theorem schurTrace : SchurTrace := schurTrace_of invInv
/- English proof (translation)
The claim follows from `typeInt_of invNat homInv schurTrace`.
-/
theorem typeInt : TypeInt := typeInt_of invNat homInv schurTrace
/- English proof (translation)
The claim follows from `fischerAdjointness_holds`.
-/
theorem fockAdj : FockAdj := fischerAdjointness_holds
/- English proof (translation)
The claim follows from `divided_integral_holds`.
-/
theorem divInt : DivInt := divided_integral_holds
/- English proof (translation)
The claim follows from `lattice_basis_polynomial`.
-/
theorem latBasisPol : LatBasisPol := lattice_basis_polynomial
/- English proof (translation)
The claim follows from `span_isomorphism_holds`.
-/
theorem spanIso : SpanIso := span_isomorphism_holds
/- English proof (translation)
The claim follows from `orthogonal_isomorphism_holds`.
-/
theorem orthIso : OrthIso := orthogonal_isomorphism_holds
/- English proof (translation)
The claim follows from `projection_lattice_holds`.
-/
theorem projP : ProjP := projection_lattice_holds
/- English proof (translation)
The claim follows from `comm_projection_holds`.
-/
theorem commP : CommP := comm_projection_holds
/- English proof (translation)
The claim follows from `intP_of typeInt latBasisPol`.
-/
theorem intP : IntP := intP_of typeInt latBasisPol
/- English proof (translation)
The claim follows from `dischargeP_of projP commP intP`.
-/
theorem dischargeP : DischargeP := dischargeP_of projP commP intP

end Formalism.InvariantFactorPaths.PW.Top
