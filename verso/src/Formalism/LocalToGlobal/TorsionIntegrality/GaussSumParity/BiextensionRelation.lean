import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SecondLevelOfNorm
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.LubinTateLogIsArtinHasse
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ComplexMultiplicationFieldData
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionRelationOfExpSpec
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.GramMatrixExists

namespace Formalism.L2.Th1.D

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ltLogIsLgF : LtLogIsLgF := lubin_tate_log_is_artin_hasse
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thetaHom : ThetaHom := theta_homomorphism
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem phCompare : PhCompare := phi_comparison
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem first_level_on_curve : CurveExponentCoboundaryCocycle := first_level_curve_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bHypCurve : BHypCurve := biextension_hypotheses_curve
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fieldDataCM : FieldDataCM := complex_multiplication_field_data
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAEntryCM : ThmAEntryCM := ThmAEntryCM_of first_level_on_curve
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAGaussCM : ThmAGaussCM := ThmAGaussCM_of first_level_on_curve
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oneLetterGaussCM : OneLetterGaussCM := OneLetterGaussCM_of first_level_on_curve
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernelCM : KernelCM := KernelCM_of first_level_on_curve
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem relative_theta_factorization : RelativeThetaFactorization := biextension_relation_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eigenOdd : EigenOdd := odd_eigenspace
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gramExists : GramExists := gram_matrix_exists

end Formalism.L2.Th1.D
