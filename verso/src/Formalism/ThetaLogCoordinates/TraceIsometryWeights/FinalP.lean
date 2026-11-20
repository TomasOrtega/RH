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
A detailed English derivation is pending.
-/
theorem invInv : InvInv := invariant_inverse_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem invNat : InvNat := invariant_natural_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem invInt : InvInt := invariant_integral_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem homRel : HomRel := hom_relation_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem homDiv : HomDiv := hom_divided_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem homTrace : HomTrace := hom_trace_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem homInv : HomInv := homInv_of invInv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem schurTrace : SchurTrace := schurTrace_of invInv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem typeInt : TypeInt := typeInt_of invNat homInv schurTrace
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fockAdj : FockAdj := fischerAdjointness_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem divInt : DivInt := divided_integral_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem latBasisPol : LatBasisPol := lattice_basis_polynomial
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem spanIso : SpanIso := span_isomorphism_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem orthIso : OrthIso := orthogonal_isomorphism_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem projP : ProjP := projection_lattice_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem commP : CommP := comm_projection_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intP : IntP := intP_of typeInt latBasisPol
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dischargeP : DischargeP := dischargeP_of projP commP intP

end Formalism.InvariantFactorPaths.PW.Top
