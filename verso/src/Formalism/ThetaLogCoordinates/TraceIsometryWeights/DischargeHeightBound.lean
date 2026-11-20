import Formalism.ThetaLogCoordinates.TraceIsometryWeights.FinalP
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.WeylInt
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.ZpClosedToAddSubgroup
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.CompEqZeroOfNotDle

namespace Formalism.InvariantFactorPaths.PW.Top

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem weylInt : WeylInt := weyl_integral_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem weylP : WeylP := weylP_of weylInt lattice_basis_polynomial

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem intP_statement : IntP := by
  have hInv : InvInv := invariant_inverse_holds
  exact intP_of (typeInt_of invariant_natural_holds (homInv_of hInv) (schurTrace_of hInv)) lattice_basis_polynomial

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem extP : ExtP := extP_of intP_statement
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dischargeW : DischargeW := dischargeW_of weylP
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dischargeE : DischargeE := dischargeE_of extP
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem discharge_height_bound : HeightBoundImplication :=
  discharge_of_pwe (dischargeP_of projection_lattice_holds comm_projection_holds intP_statement) dischargeW dischargeE

end Formalism.InvariantFactorPaths.PW.Top
