import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.XTwoDvdOfRestrictThirdZero
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Wp3ApplyEqSqMulSubSqMul
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.RealAdelicInertTransportTypeFormsEqAlt
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffLawWithInverseThree
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.FirstLevelOfThreeVarParallelogram
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveCocycleIntegralAllResidues

namespace Formalism.L2.Th1.B

open Formalism.L2.Th1.A (bridgeWp bridgeLaw bridgeCurve bridgeCurve3)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem shearLemma : ShearLemma := Wr.shearedWronskianUniqueness
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tauRule : TauRule := Det.tau_derivative_rule_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem detRule : DetRule := Det.determinant_derivative_rule_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frobStickLog : FrobStickLog := Fs.FrobStickLog_of shearLemma tauRule detRule
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frobStick : FrobStick := Fs.FrobStick_of frobStickLog
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frobStickStar : FrobStickStar := Fs.FrobStickStar_of frobStick
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fIUnit : FIUnit := E2.formal_inverse_unit_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem parThree : ParThree := E2.ParThree_of frobStickStar fIUnit
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cubeFromPars : CubeFromPars := E3.cube_relation_from_parallelograms
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem first_level_all_formal_groups : LogSigmaPullbackCocycleJets := E3.log_sigma_pullback_cocycle_jets_of_parallelogram_and_cube parThree cubeFromPars

end Formalism.L2.Th1.B
