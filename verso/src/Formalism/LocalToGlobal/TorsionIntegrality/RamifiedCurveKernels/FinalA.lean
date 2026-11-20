import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.HurwitzB
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.InverseEndoIntegralHolds
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.CurveFormalFirstLevelHolds
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Several
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Kernel
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.ConstantCoeffCMulSqSum

namespace Formalism.L2.Th1.G

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jetsInNorm : JetsInNorm := jets_in_norm_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jetsRing : JetsRing := jets_ring_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jetsExp : JetsExp := jets_exp_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jetsFourth : JetsFourth := jets_fourth_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intDJets : IntDJets := integral_dist_jets_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem invEndInt : InvEndInt := inverse_endo_integral_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem adjUnitNorm : AdjUnitNorm := adjoint_unit_norm_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ramifiedShape : RamifiedShape := ramified_shape_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem curveNegNorm : CurveNegNorm := curve_neg_norm_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem weierstrass_biadditive_mod_equiv : WeierstrassBiadditiveModEquiv := curve_formal_first_level_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem curveRamified : CurveRamified := CurveRamified_of_shape ramifiedShape adjUnitNorm invEndInt

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eigenSplit : EigenSplit := eigen_split_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem shapeCong : ShapeCong := shape_congruence_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem shapeOrth : ShapeOrth := shape_orthogonal_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intAtD : IntAtD := IntAtD_of shapeOrth

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernelShape : KernelShape := KernelShape_of shapeOrth shapeCong
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernelThmB : KernelThmB := KernelThmB_of kernelShape
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernelThmBGauss : KernelThmBGauss := KernelThmBGauss_of kernelShape

end Formalism.L2.Th1.G
