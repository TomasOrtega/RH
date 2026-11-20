import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.ConstantCoeffVecConsPairEqZero
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.SigmaConstantAgrees
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.TraceDiagonalBis
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.IntegralThirdInvariantDerivative

namespace Formalism.L2.Th1.C

/- English proof (translation)
The claim follows from `simeq_iff_congruence`.
-/
theorem simeqIffCong : SimeqIffCong := simeq_iff_congruence
/- English proof (translation)
The claim follows from `unit_ball_closed`.
-/
theorem unitBallClosed : UnitBallClosed := unit_ball_closed
/- English proof (translation)
The claim follows from `odd_phi_is_phi`.
-/
theorem phOIsPh : PhOIsPh := odd_phi_is_phi
/- English proof (translation)
The claim follows from `first_level_from_universal_holds`.
-/
theorem first_level_from_universal_law : FirstLevelFromUniversal := first_level_from_universal_holds

/- English proof (translation)
The claim follows from `all_jets_integral`.
-/
theorem jetsAll : JetsAll := all_jets_integral

/- English proof (translation)
The claim follows from `gram_formula`.
-/
theorem gramFormula : GramFormula := gram_formula

/- English proof (translation)
The claim follows from `log_derivative_integral'`.
-/
theorem logDerivInt : LogDerivInt := log_derivative_integral'
/- English proof (translation)
The claim follows from `third_jet_integral`.
-/
theorem derivation_cube_integral_jet : ThirdJetIntegral := third_jet_integral
/- English proof (translation)
The claim follows from `jets_unramified`.
-/
theorem jetsUnramified : JetsUnramified := jets_unramified
/- English proof (translation)
The claim follows from `jets_shape`.
-/
theorem jetsShape : JetsShape := jets_shape

end Formalism.L2.Th1.C
