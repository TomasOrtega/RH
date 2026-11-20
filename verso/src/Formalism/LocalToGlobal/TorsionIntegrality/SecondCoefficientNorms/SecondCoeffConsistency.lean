import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.DegreeLeOfMemAntidiagonal
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.ConstantCoeffSubstBinomSeries
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.HasSecondLogDerivPowerSeriesExp
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.SecondCoeffConsistency
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.USideA
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.USideB

namespace Formalism.L2.Th1.C

/- English proof (translation)
The claim follows from `formalExpLaws'`.
-/
theorem mvExpLaws : MvExpLaws := formalExpLaws'
/- English proof (translation)
The claim follows from `formalExpSubst'`.
-/
theorem mvExpSubst : MvExpSubst := formalExpSubst'
/- English proof (translation)
The claim follows from `lGSubgroup_of mvExpLaws`.
-/
theorem lGSubgroup : LGSubgroup := lGSubgroup_of mvExpLaws
/- English proof (translation)
The claim follows from `expIntegralBinomial'`.
-/
theorem lGBinom : LGBinom := expIntegralBinomial'
/- English proof (translation)
The claim follows from `lGHalf_of mvExpLaws`.
-/
theorem lGHalf : LGHalf := lGHalf_of mvExpLaws
/- English proof (translation)
The claim follows from `intBinomialScalar'`.
-/
theorem intBinomScalar : IntBinomScalar := intBinomialScalar'
/- English proof (translation)
The claim follows from `lGSubst_of mvExpSubst`.
-/
theorem lGSubst : LGSubst := lGSubst_of mvExpSubst
/- English proof (translation)
The claim follows from `expIntegralMvSubst'`.
-/
theorem lGSubstMv : LGSubstMv := expIntegralMvSubst'
/- English proof (translation)
The claim follows from `coeffsInSubst'`.
-/
theorem intSubst : IntSubst := coeffsInSubst'

/- English proof (translation)
The claim follows from `isogenyIffBar_of mvExpLaws`.
-/
theorem isogenyIffBar : IsogenyIffBar := isogenyIffBar_of mvExpLaws

/- English proof (translation)
The claim follows from `veluXOfSigma'`.
-/
theorem veluXFromZ : VeluXFromZ := veluXOfSigma'
/- English proof (translation)
The claim follows from `isogenyU_of mvExpLaws mvExpSubst`.
-/
theorem isogenyU : IsogenyU := isogenyU_of mvExpLaws mvExpSubst
/- English proof (translation)
The claim follows from `phNormUnit_of mvExpLaws mvExpSubst lGHalf isogenyU`.
-/
theorem phNormUnit : PhNormUnit := phNormUnit_of mvExpLaws mvExpSubst lGHalf isogenyU

end Formalism.L2.Th1.C
