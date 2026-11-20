import Formalism.ThetaLogCoordinates.TraceIsometryWeights.FinalP
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.WeylInt
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.ZpClosedToAddSubgroup
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.CompEqZeroOfNotDle

namespace Formalism.InvariantFactorPaths.PW.Top

/- English proof (translation)
The claim follows from `weyl_integral_holds`.
-/
theorem weylInt : WeylInt := weyl_integral_holds
/- English proof (translation)
The claim follows from `weylP_of weylInt lattice_basis_polynomial`.
-/
theorem weylP : WeylP := weylP_of weylInt lattice_basis_polynomial

/- English proof (translation)
Establish `hInv : InvInv` using `invariant_inverse_holds`. Conclude with `intP_of (typeInt_of invariant_natural_holds (homInv_of hInv) (schurTrace_of hInv)) lattice_basis_polynomial`.
-/
private theorem intP_statement : IntP := by
  have hInv : InvInv := invariant_inverse_holds
  exact intP_of (typeInt_of invariant_natural_holds (homInv_of hInv) (schurTrace_of hInv)) lattice_basis_polynomial

/- English proof (translation)
The claim follows from `extP_of intP_statement`.
-/
theorem extP : ExtP := extP_of intP_statement
/- English proof (translation)
The claim follows from `dischargeW_of weylP`.
-/
theorem dischargeW : DischargeW := dischargeW_of weylP
/- English proof (translation)
The claim follows from `dischargeE_of extP`.
-/
theorem dischargeE : DischargeE := dischargeE_of extP
/- English proof (translation)
The claim follows from `discharge_of_pwe (dischargeP_of projection_lattice_holds comm_projection_holds intP_statement) dischargeW dischargeE`.
-/
theorem discharge_height_bound : HeightBoundImplication :=
  discharge_of_pwe (dischargeP_of projection_lattice_holds comm_projection_holds intP_statement) dischargeW dischargeE

end Formalism.InvariantFactorPaths.PW.Top
