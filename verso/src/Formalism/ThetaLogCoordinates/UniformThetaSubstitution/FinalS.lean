import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartB
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LocalComponentGL
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TheoremSFromKOneOf
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.CoeffSubstLgFOfDegreeOne
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.IntegralPderivLgF
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.NotDvdChoosePowMul
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LemmaTwoOf
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.ScalingSwapLemmas
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.ConstantCoeffLawFirstTwoOfThree
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.PartialCoboundaryLinear
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.ConstantCoeffFirstTwoOfThree
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.NormLiftLeOne

namespace Formalism.InvariantFactorPaths.G7.Top

open Formalism.InvariantFactorPaths.G7

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem g_zero_relation : OddLogRelation := g_zero_relation_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem identityB : IdentityB := identity_b
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frobExprG : FrobExprG := frobenius_expression_g
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem valTable : ValTable := valuation_table
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem piFactorial : PiFactorial := pi_factorial
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem expIntegral : ExpIntegral := exp_integral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem classChange : ClassChange := classChange_statement
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem classMul : ClassMul := class_multiplication
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem classSubst : ClassSubst := class_substitution
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem classExp : ClassExp := class_exponential
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rescaleExact : RescaleExact := RescaleExact_of valTable expIntegral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rescaleCore : RescaleCore := RescaleCore_of rescaleExact classExp classMul

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dworkMv : DworkMv := dwork_multivariable
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem simeqRules : SimeqRules := equivalence_rules
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem logRescale : LogRescale := log_rescale_alt
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem logRescaleUnique : LogRescaleUnique := log_rescale_unique
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem traceDual : TraceDual := trace_duality
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem twoSums : TwoSums := two_sums
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmSCore : ThmSCore :=
  ThmSCore_of rescaleCore classSubst classChange classMul twoSums logRescale logRescaleUnique
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem theorem_s_from_k_one : CyclicPowerClassOfExpEquiv := theorem_s_from_k_one_of thmSCore simeqRules

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lawExists : LawExists := formal_law_exists
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lawSymm : LawSymm := formal_law_symmetric
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem divDeriv : DivDeriv := divided_derivative
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem deIntegral : DeIntegral := DeIntegral_of divDeriv lawSymm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem derivA : DerivA := derivative_a
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemmaOne : LemmaOne := LemmaOne_of deIntegral lawSymm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemmaTwo : LemmaTwo := LemmaTwo_of lemmaOne lawSymm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lamModule : LamModule := LamModule_of dworkMv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zeroCondition : StepZero := StepZero_of lamModule simeqRules lawSymm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem firstDeriv : FirstDeriv := FirstDeriv_of lawSymm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cobLin : CobLin := CobLin_of lawSymm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stepI : StepI := StepI_of lemmaOne firstDeriv cobLin
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stepII : StepII := StepII_of dworkMv divDeriv deIntegral lawSymm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem swapRules : SwapRules := swap_rules
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stepH : StepH := StepH_of lemmaTwo swapRules lawSymm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stepIII : StepIII := c_add_sigma_c_eq_zero
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stepIV : StepIV := StepIV_of dworkMv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mapSimeq : MapSimeq := mapSimeq_statement
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem betaIsG : BetaIsG :=
  BetaIsG_of zeroCondition stepI stepII stepH stepIII stepIV swapRules simeqRules
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmSFull : ThmSFull := ThmSFull_of betaIsG theorem_s_from_k_one mapSimeq

end Formalism.InvariantFactorPaths.G7.Top
