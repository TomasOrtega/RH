import Formalism.EllipticTorsion.EllipticTorsionProofs.LegendreInvariant
import Formalism.EllipticTorsion.EllipticTorsionProofs.Legendre
import Formalism.EllipticTorsion.EllipticTorsionProofs.Deuring
import Formalism.EllipticTorsion.EllipticTorsionProofs.ModelUnitOf
import Formalism.EllipticTorsion.EllipticTorsionProofs.IntVal
import Formalism.EllipticTorsion.EllipticTorsionProofs.PadicMult
import Formalism.EllipticTorsion.EllipticTorsionProofs.ConstantCoeffLogOnePlus
import Formalism.EllipticTorsion.EllipticTorsionProofs.IntegralPSBserSubOne
import Formalism.EllipticTorsion.EllipticTorsionProofs.NDeriv
import Formalism.EllipticTorsion.EllipticTorsionProofs.JetsCube
import Formalism.EllipticTorsion.EllipticTorsionProofs.JetsTwo
import Formalism.EllipticTorsion.EllipticTorsionProofs.JetsOne
import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsSubgroupHolds
import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsNoPrimeToPTorsion
import Formalism.EllipticTorsion.EllipticTorsionProofs.TorInt
import Formalism.EllipticTorsion.EllipticTorsionProofs.IsogenyExpansion
import Formalism.EllipticTorsion.EllipticTorsionProofs.Change
import Formalism.EllipticTorsion.EllipticTorsionProofs.UnitCancel
import Formalism.EllipticTorsion.EllipticTorsionProofs.LogWeight
import Formalism.EllipticTorsion.EllipticTorsionProofs.ExpWeight
import Formalism.EllipticTorsion.EllipticTorsionProofs.CompExp
import Formalism.EllipticTorsion.EllipticTorsionProofs.CoefficientWeightsLemmaTwo
import Formalism.EllipticTorsion.EllipticTorsionProofs.ExistsSumPowPrimePow
import Formalism.EllipticTorsion.EllipticTorsionProofs.WSeries
import Formalism.EllipticTorsion.EllipticTorsionProofs.WPoint
import Formalism.EllipticTorsion.EllipticTorsionProofs.WChord
import Formalism.EllipticTorsion.EllipticTorsionProofs.WSubst
import Formalism.EllipticTorsion.EllipticTorsionProofs.ExistsUnitFactor
import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsParamDef
import Formalism.EllipticTorsion.EllipticTorsionProofs.VeluInt
import Formalism.EllipticTorsion.EllipticTorsionProofs.VeluUSeries
import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsHomDef
import Formalism.EllipticTorsion.EllipticTorsionProofs.CubeTwo
import Formalism.EllipticTorsion.EllipticTorsionProofs.CubeThree

universe u

namespace Formalism.ELL

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem legendreInv : LegendreInv.{u} := legendre_invariant
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem deuringInv : DeuringInv.{u} := deuring_invariant
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem modelLegendre : ModelLegendre.{u} := legendre_model
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem modelDeuring : ModelDeuring.{u} := deuring_model
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem modelUnit : ModelUnit.{u} := by
  apply modelUnit_of <;> first | exact modelLegendre | exact modelDeuring | exact legendreInv | exact deuringInv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intValuedZp : IntValuedZp.{u} := integer_valued_padic_integers
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem padicMult : PadicMult.{u} := by
  apply padicMult_of <;> first | exact intValuedZp | exact nAddSubgroup | exact nZpSmul | exact nPderiv | exact lwP₂ | exact unitCancel | exact compExpWeight | exact lemma2Weights | exact frobExpand | exact wFormalGroup | exact formal_group_points_subgroup | exact formal_group_points_no_torsion | exact isoExpand | exact isoVanish | exact changeIntegral | exact wPoint | exact wSubstUnique | exact wChordSubst | exact wChordSeries | exact veluIntegralModel | exact veluUSeries | exact modelUnit
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nAddSubgroup : NAddSubgroup.{u} := N_additive_subgroup
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nZpSmul : NZpSmul.{u} := N_padic_integer_smul
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nPderiv : NPderiv.{u} := N_partial_derivative

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jetsCube : JetsCube.{u} := jetsCube_of N_partial_derivative
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jetsTwo : JetsTwo.{u} := jetsTwo_of nPderiv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jetsOne : JetsOne.{u} := jetsOne_of N_partial_derivative

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem formal_group_points_subgroup : FormalGroupPointsSubgroup'.{u} := formal_group_points_subgroup_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem formal_group_points_no_torsion : FormalGroupPointsTorsionFree.{u} := formal_group_points_no_prime_to_p_torsion
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem torsionIntegral : TorsionIntegral.{u} := torsionIntegral_of formal_group_points_no_torsion

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isoExpand : IsoExpand.{u} := isogeny_expansion
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isoVanish : IsoVanish.{u} := isogeny_vanishing

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem changeIntegral : ChangeIntegral.{u} := change_of_variables_integral

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lwP₂ : LogWeight.{u} := logarithm_coeff_weight
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem expWeight : ExpWeight.{u} := by
  apply expWeight_of <;> first | exact intValuedZp | exact nAddSubgroup | exact nZpSmul | exact nPderiv | exact lwP₂ | exact unitCancel | exact compExpWeight | exact lemma2Weights | exact frobExpand | exact wFormalGroup | exact formal_group_points_subgroup | exact formal_group_points_no_torsion | exact isoExpand | exact isoVanish | exact changeIntegral | exact wPoint | exact wSubstUnique | exact wChordSubst | exact wChordSeries | exact veluIntegralModel | exact veluUSeries | exact modelUnit
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unitCancel : UnitCancel.{u} := unit_cancellation

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem compExpWeight : CompExpWeight.{u} := comp_exp_coeff_weight

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemma2Weights : EllipticTorsionWeights.{u} := coefficient_weights_lemma_two
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frobExpand : FrobExpand.{u} := frobenius_expansion

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wSeriesUnique : WSeriesUnique.{u} := wSeriesExistsUnique_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wSeriesLead : WSeriesLead.{u} := wSeriesLeadingTerm_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wSubstUnique : WSubstUnique.{u} := wSeriesSubstUnique_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wPoint : WPoint.{u} := wSeriesNonsingularPoint_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wChordSeries : WChordSeries.{u} := wChordSeries_of wSubstUnique
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wChordSubst : WChordSubst.{u} := wChordSubst_of wSeriesSubstUnique_holds
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem wFormalGroup : WFormalGroup.{u} := by
  apply wFormalGroup_of <;> first | exact wChordSeries | exact wChordSubst | exact wPoint | exact wSubstUnique | exact wSeriesUnique | exact wSeriesLead

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem formal_group_points_param : FormalGroupPointsParametrisation.{u} := by
  apply formal_group_points_param_of <;> first | exact intValuedZp | exact nAddSubgroup | exact nZpSmul | exact nPderiv | exact lwP₂ | exact unitCancel | exact compExpWeight | exact lemma2Weights | exact frobExpand | exact wFormalGroup | exact formal_group_points_subgroup | exact formal_group_points_no_torsion | exact isoExpand | exact isoVanish | exact changeIntegral | exact wPoint | exact wSubstUnique | exact wChordSubst | exact wChordSeries | exact veluIntegralModel | exact veluUSeries | exact modelUnit
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem formal_group_points_hom : FormalGroupPointsHomomorphism.{u} := by
  apply formal_group_points_hom_of <;> first | exact wSubstUnique | exact wChordSubst | exact formal_group_points_param | exact wFormalGroup | exact wChordSeries | exact wPoint

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem veluIntegralModel : VeluIntegralModel.{u} := velu_integral_model
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem veluUSeries : VeluUSeries.{u} := velu_u_series

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cubeTwo : CubeTwo.{u} := cube_two
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cubeThree : CubeThree.{u} := chordDeterminantFactor_holds

end Formalism.ELL
