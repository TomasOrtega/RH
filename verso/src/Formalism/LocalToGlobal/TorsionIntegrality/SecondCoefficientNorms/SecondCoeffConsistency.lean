import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.DegreeLeOfMemAntidiagonal
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.ConstantCoeffSubstBinomSeries
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.HasSecondLogDerivPowerSeriesExp
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.SecondCoeffConsistency
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.USideA
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.USideB

namespace Formalism.L2.Th1.C

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mvExpLaws : MvExpLaws := formalExpLaws'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mvExpSubst : MvExpSubst := formalExpSubst'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lGSubgroup : LGSubgroup := lGSubgroup_of mvExpLaws
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lGBinom : LGBinom := expIntegralBinomial'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lGHalf : LGHalf := lGHalf_of mvExpLaws
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intBinomScalar : IntBinomScalar := intBinomialScalar'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lGSubst : LGSubst := lGSubst_of mvExpSubst
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lGSubstMv : LGSubstMv := expIntegralMvSubst'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intSubst : IntSubst := coeffsInSubst'

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isogenyIffBar : IsogenyIffBar := isogenyIffBar_of mvExpLaws

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem veluXFromZ : VeluXFromZ := veluXOfSigma'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isogenyU : IsogenyU := isogenyU_of mvExpLaws mvExpSubst
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem phNormUnit : PhNormUnit := phNormUnit_of mvExpLaws mvExpSubst lGHalf isogenyU

end Formalism.L2.Th1.C
