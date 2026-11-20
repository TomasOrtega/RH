import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.SigmaOneCocycleShifted
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.MultiplicationBiadditiveHolds
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BaseChangeCompatible
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.NormHalfB2SubTwoTorsionLeOne

namespace Formalism.L2.Th1.B

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem phESimPhO : PhESimPhO := Cor.even_phi_simeq_odd_phi
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem f1EW : SigmaOneCocycleShifted := Cor.sigma_one_cocycle_shifted
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jetOne : JetOne := Cor.first_jet_of_formal_law
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jetsPhO : JetsPhO := Cor.jets_of_odd_parallelogram_phi
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mulExists : MulExists := Mul.formal_multiplication_exists
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mulSq : MulSq := Mul.multiplication_square_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem addMul : AddMul := Mul.multiplication_additive_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem biaddMul : BiaddMul := Mul.multiplication_biadditive_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem baseChange : BaseChange := Map.baseChangeCompatible
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem curveSigma : CurveSigma := Crv.curve_sigma_function_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem curvePar : CurvePar := Crv.CurvePar_of mulSq
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem weierstrass_biadditive_mod_equiv : WeierstrassBiadditiveModEquiv := Crv.curve_formal_first_level_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem curveJets : CurveJets := Crv.curve_formal_jets_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem curveTwo : CurveTwo := Crv.curve_two_torsion_formal
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem curveTwoOdd : CurveTwoOdd := Crv.curve_two_torsion_odd_holds

end Formalism.L2.Th1.B
