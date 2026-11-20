import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.SigmaOneCocycleShifted
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.MultiplicationBiadditiveHolds
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BaseChangeCompatible
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.NormHalfB2SubTwoTorsionLeOne

namespace Formalism.L2.Th1.B

/- English proof (translation)
The claim follows from `Cor.even_phi_simeq_odd_phi`.
-/
theorem phESimPhO : PhESimPhO := Cor.even_phi_simeq_odd_phi
/- English proof (translation)
The claim follows from `Cor.sigma_one_cocycle_shifted`.
-/
theorem f1EW : SigmaOneCocycleShifted := Cor.sigma_one_cocycle_shifted
/- English proof (translation)
The claim follows from `Cor.first_jet_of_formal_law`.
-/
theorem jetOne : JetOne := Cor.first_jet_of_formal_law
/- English proof (translation)
The claim follows from `Cor.jets_of_odd_parallelogram_phi`.
-/
theorem jetsPhO : JetsPhO := Cor.jets_of_odd_parallelogram_phi
/- English proof (translation)
The claim follows from `Mul.formal_multiplication_exists`.
-/
theorem mulExists : MulExists := Mul.formal_multiplication_exists
/- English proof (translation)
The claim follows from `Mul.multiplication_square_holds`.
-/
theorem mulSq : MulSq := Mul.multiplication_square_holds
/- English proof (translation)
The claim follows from `Mul.multiplication_additive_holds`.
-/
theorem addMul : AddMul := Mul.multiplication_additive_holds
/- English proof (translation)
The claim follows from `Mul.multiplication_biadditive_holds`.
-/
theorem biaddMul : BiaddMul := Mul.multiplication_biadditive_holds
/- English proof (translation)
The claim follows from `Map.baseChangeCompatible`.
-/
theorem baseChange : BaseChange := Map.baseChangeCompatible
/- English proof (translation)
The claim follows from `Crv.curve_sigma_function_holds`.
-/
theorem curveSigma : CurveSigma := Crv.curve_sigma_function_holds
/- English proof (translation)
The claim follows from `Crv.CurvePar_of mulSq`.
-/
theorem curvePar : CurvePar := Crv.CurvePar_of mulSq
/- English proof (translation)
The claim follows from `Crv.curve_formal_first_level_holds`.
-/
theorem weierstrass_biadditive_mod_equiv : WeierstrassBiadditiveModEquiv := Crv.curve_formal_first_level_holds
/- English proof (translation)
The claim follows from `Crv.curve_formal_jets_holds`.
-/
theorem curveJets : CurveJets := Crv.curve_formal_jets_holds
/- English proof (translation)
The claim follows from `Crv.curve_two_torsion_formal`.
-/
theorem curveTwo : CurveTwo := Crv.curve_two_torsion_formal
/- English proof (translation)
The claim follows from `Crv.curve_two_torsion_odd_holds`.
-/
theorem curveTwoOdd : CurveTwoOdd := Crv.curve_two_torsion_odd_holds

end Formalism.L2.Th1.B
