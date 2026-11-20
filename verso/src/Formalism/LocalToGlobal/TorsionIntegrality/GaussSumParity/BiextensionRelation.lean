import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SecondLevelOfNorm
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.LubinTateLogIsArtinHasse
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ComplexMultiplicationFieldData
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionRelationOfExpSpec
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.GramMatrixExists

namespace Formalism.L2.Th1.D

/- English proof (translation)
The claim follows from `lubin_tate_log_is_artin_hasse`.
-/
theorem ltLogIsLgF : LtLogIsLgF := lubin_tate_log_is_artin_hasse
/- English proof (translation)
The claim follows from `theta_homomorphism`.
-/
theorem thetaHom : ThetaHom := theta_homomorphism
/- English proof (translation)
The claim follows from `phi_comparison`.
-/
theorem phCompare : PhCompare := phi_comparison
/- English proof (translation)
The claim follows from `first_level_curve_holds`.
-/
theorem first_level_on_curve : CurveExponentCoboundaryCocycle := first_level_curve_holds
/- English proof (translation)
The claim follows from `biextension_hypotheses_curve`.
-/
theorem bHypCurve : BHypCurve := biextension_hypotheses_curve
/- English proof (translation)
The claim follows from `complex_multiplication_field_data`.
-/
theorem fieldDataCM : FieldDataCM := complex_multiplication_field_data
/- English proof (translation)
The claim follows from `ThmAEntryCM_of first_level_on_curve`.
-/
theorem thmAEntryCM : ThmAEntryCM := ThmAEntryCM_of first_level_on_curve
/- English proof (translation)
The claim follows from `ThmAGaussCM_of first_level_on_curve`.
-/
theorem thmAGaussCM : ThmAGaussCM := ThmAGaussCM_of first_level_on_curve
/- English proof (translation)
The claim follows from `OneLetterGaussCM_of first_level_on_curve`.
-/
theorem oneLetterGaussCM : OneLetterGaussCM := OneLetterGaussCM_of first_level_on_curve
/- English proof (translation)
The claim follows from `KernelCM_of first_level_on_curve`.
-/
theorem kernelCM : KernelCM := KernelCM_of first_level_on_curve
/- English proof (translation)
The claim follows from `biextension_relation_holds`.
-/
theorem relative_theta_factorization : RelativeThetaFactorization := biextension_relation_holds
/- English proof (translation)
The claim follows from `odd_eigenspace`.
-/
theorem eigenOdd : EigenOdd := odd_eigenspace
/- English proof (translation)
The claim follows from `gram_matrix_exists`.
-/
theorem gramExists : GramExists := gram_matrix_exists

end Formalism.L2.Th1.D
