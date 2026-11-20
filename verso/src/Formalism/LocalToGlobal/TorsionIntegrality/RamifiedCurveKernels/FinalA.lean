import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.HurwitzB
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.InverseEndoIntegralHolds
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.CurveFormalFirstLevelHolds
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Several
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Kernel
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.ConstantCoeffCMulSqSum

namespace Formalism.L2.Th1.G

/- English proof (translation)
The claim follows from `jets_in_norm_holds`.
-/
theorem jetsInNorm : JetsInNorm := jets_in_norm_holds
/- English proof (translation)
The claim follows from `jets_ring_holds`.
-/
theorem jetsRing : JetsRing := jets_ring_holds
/- English proof (translation)
The claim follows from `jets_exp_holds`.
-/
theorem jetsExp : JetsExp := jets_exp_holds
/- English proof (translation)
The claim follows from `jets_fourth_holds`.
-/
theorem jetsFourth : JetsFourth := jets_fourth_holds
/- English proof (translation)
The claim follows from `integral_dist_jets_holds`.
-/
theorem intDJets : IntDJets := integral_dist_jets_holds

/- English proof (translation)
The claim follows from `inverse_endo_integral_holds`.
-/
theorem invEndInt : InvEndInt := inverse_endo_integral_holds
/- English proof (translation)
The claim follows from `adjoint_unit_norm_holds`.
-/
theorem adjUnitNorm : AdjUnitNorm := adjoint_unit_norm_holds
/- English proof (translation)
The claim follows from `ramified_shape_holds`.
-/
theorem ramifiedShape : RamifiedShape := ramified_shape_holds
/- English proof (translation)
The claim follows from `curve_neg_norm_holds`.
-/
theorem curveNegNorm : CurveNegNorm := curve_neg_norm_holds
/- English proof (translation)
The claim follows from `curve_formal_first_level_holds`.
-/
theorem weierstrass_biadditive_mod_equiv : WeierstrassBiadditiveModEquiv := curve_formal_first_level_holds
/- English proof (translation)
The claim follows from `CurveRamified_of_shape ramifiedShape adjUnitNorm invEndInt`.
-/
theorem curveRamified : CurveRamified := CurveRamified_of_shape ramifiedShape adjUnitNorm invEndInt

/- English proof (translation)
The claim follows from `eigen_split_holds`.
-/
theorem eigenSplit : EigenSplit := eigen_split_holds
/- English proof (translation)
The claim follows from `shape_congruence_holds`.
-/
theorem shapeCong : ShapeCong := shape_congruence_holds
/- English proof (translation)
The claim follows from `shape_orthogonal_holds`.
-/
theorem shapeOrth : ShapeOrth := shape_orthogonal_holds
/- English proof (translation)
The claim follows from `IntAtD_of shapeOrth`.
-/
theorem intAtD : IntAtD := IntAtD_of shapeOrth

/- English proof (translation)
The claim follows from `KernelShape_of shapeOrth shapeCong`.
-/
theorem kernelShape : KernelShape := KernelShape_of shapeOrth shapeCong
/- English proof (translation)
The claim follows from `KernelThmB_of kernelShape`.
-/
theorem kernelThmB : KernelThmB := KernelThmB_of kernelShape
/- English proof (translation)
The claim follows from `KernelThmBGauss_of kernelShape`.
-/
theorem kernelThmBGauss : KernelThmBGauss := KernelThmBGauss_of kernelShape

end Formalism.L2.Th1.G
