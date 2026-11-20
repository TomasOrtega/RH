import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SecondCoeffConsistency
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.UnitaryInverseIdentity
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Closure
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.IntPSDerivativeOfLG
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.IntegralEndomorphismFromDatum

namespace Formalism.L2.Th1.C

/- English proof (translation)
The claim follows from `integralPointClosure'`.
-/
theorem ptClosure : PtClosure := integralPointClosure'
/- English proof (translation)
The claim follows from `adjoint_from_norm_form`.
-/
theorem adjFromNorm : AdjFromNorm := adjoint_from_norm_form
/- English proof (translation)
The claim follows from `norm_adjoint_all_places`.
-/
theorem normAdjAll : NormAdjAll := norm_adjoint_all_places
/- English proof (translation)
The claim follows from `unitary_inverse_identity`.
-/
theorem unitaryInv : UnitaryInv := unitary_inverse_identity
/- English proof (translation)
The claim follows from `hyperbolic_sum_identity`.
-/
theorem hyperbolicSum : HyperbolicSum := hyperbolic_sum_identity

/- English proof (translation)
The claim follows from `integralEndoClosed'`.
-/
theorem endIntClosed : EndIntClosed := integralEndoClosed'
/- English proof (translation)
The claim follows from `binomialScalarClosed'`.
-/
theorem binomClosed : BinomClosed := binomialScalarClosed'
/- English proof (translation)
The claim follows from `logNormClosed'`.
-/
theorem phNormClosed : PhNormClosed := logNormClosed'
/- English proof (translation)
The claim follows from `scalarLinearClosed'`.
-/
theorem zLinClosed : ZLinClosed := scalarLinearClosed'
/- English proof (translation)
The claim follows from `scalarLinearInt'`.
-/
theorem zLinInt : ZLinInt := scalarLinearInt'
/- English proof (translation)
The claim follows from `endoAll_of normAdjAll`.
-/
theorem endoAll : EndoAll := endoAll_of normAdjAll

/- English proof (translation)
The claim follows from `jetAdditivity`.
-/
theorem jetAdditive : JetAdditive := jetAdditivity
/- English proof (translation)
The claim follows from `jetOne'`.
-/
theorem jetOne : JetOne := jetOne'
/- English proof (translation)
The claim follows from `jetAdjoint'`.
-/
theorem jetAdj : JetAdj := jetAdjoint'
/- English proof (translation)
The claim follows from `jetExp'`.
-/
theorem jetExp : JetExp := jetExp'

/- English proof (translation)
The claim follows from `integral_endomorphism_from_datum`.
-/
theorem endIntFromDatum : EndIntFromDatum := integral_endomorphism_from_datum
/- English proof (translation)
The claim follows from `phi_norm_from_datum`.
-/
theorem phNormFromDatum : PhNormFromDatum := phi_norm_from_datum
/- English proof (translation)
The claim follows from `endoAllFromData_of endoAll`.
-/
theorem endoAllFromData : EndoAllFromData := endoAllFromData_of endoAll

end Formalism.L2.Th1.C
