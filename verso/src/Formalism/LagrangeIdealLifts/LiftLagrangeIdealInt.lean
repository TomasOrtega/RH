import Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.LagrangeIdeal
import Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.LagrangeIdealCyc
import Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.Graded
import Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.CompsOfMemMap
import Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.UClaim
import Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.UChase
import Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.CoeffSumXPowMulExpand

namespace Formalism.LIFT

/- English proof (translation)
The claim follows from `lagrangian_ideal_holds`.
-/
theorem lift_LagrangeIdeal : LagrangeIdeal := lagrangian_ideal_holds
/- English proof (translation)
The claim follows from `lagrangian_ideal_integral_holds`.
-/
theorem lift_LagrangeIdealInt : LagrangeIdealInt := lagrangian_ideal_integral_holds
/- English proof (translation)
The claim follows from `wBTail_of gammaGradedStep_holds (lagrangeIdealCyc_of lagrangian_ideal_holds)`.
-/
theorem lift_WBTail : WBTail := wBTail_of gammaGradedStep_holds (lagrangeIdealCyc_of lagrangian_ideal_holds)
/- English proof (translation)
The claim follows from `lemmaU_of (uClaim_of (uGraded_of gammaGradedStep_holds) gammaGradedStep_holds) uChase_proof`.
-/
theorem lift_LemmaU : LemmaU := lemmaU_of (uClaim_of (uGraded_of gammaGradedStep_holds) gammaGradedStep_holds) uChase_proof

end Formalism.LIFT
