import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SecondCoeffConsistency
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.UnitaryInverseIdentity
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Closure
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.IntPSDerivativeOfLG
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.IntegralEndomorphismFromDatum

namespace Formalism.L2.Th1.C

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ptClosure : PtClosure := integralPointClosure'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem adjFromNorm : AdjFromNorm := adjoint_from_norm_form
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem normAdjAll : NormAdjAll := norm_adjoint_all_places
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unitaryInv : UnitaryInv := unitary_inverse_identity
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hyperbolicSum : HyperbolicSum := hyperbolic_sum_identity

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem endIntClosed : EndIntClosed := integralEndoClosed'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem binomClosed : BinomClosed := binomialScalarClosed'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem phNormClosed : PhNormClosed := logNormClosed'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zLinClosed : ZLinClosed := scalarLinearClosed'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zLinInt : ZLinInt := scalarLinearInt'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem endoAll : EndoAll := endoAll_of normAdjAll

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jetAdditive : JetAdditive := jetAdditivity
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jetOne : JetOne := jetOne'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jetAdj : JetAdj := jetAdjoint'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jetExp : JetExp := jetExp'

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem endIntFromDatum : EndIntFromDatum := integral_endomorphism_from_datum
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem phNormFromDatum : PhNormFromDatum := phi_norm_from_datum
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem endoAllFromData : EndoAllFromData := endoAllFromData_of endoAll

end Formalism.L2.Th1.C
