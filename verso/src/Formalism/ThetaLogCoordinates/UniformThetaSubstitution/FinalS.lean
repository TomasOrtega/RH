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
The claim follows from `g_zero_relation_holds`.
-/
theorem g_zero_relation : OddLogRelation := g_zero_relation_holds
/- English proof (translation)
The claim follows from `identity_b`.
-/
theorem identityB : IdentityB := identity_b
/- English proof (translation)
The claim follows from `frobenius_expression_g`.
-/
theorem frobExprG : FrobExprG := frobenius_expression_g
/- English proof (translation)
The claim follows from `valuation_table`.
-/
theorem valTable : ValTable := valuation_table
/- English proof (translation)
The claim follows from `pi_factorial`.
-/
theorem piFactorial : PiFactorial := pi_factorial
/- English proof (translation)
The claim follows from `exp_integral`.
-/
theorem expIntegral : ExpIntegral := exp_integral
/- English proof (translation)
The claim follows from `classChange_statement`.
-/
theorem classChange : ClassChange := classChange_statement
/- English proof (translation)
The claim follows from `class_multiplication`.
-/
theorem classMul : ClassMul := class_multiplication
/- English proof (translation)
The claim follows from `class_substitution`.
-/
theorem classSubst : ClassSubst := class_substitution
/- English proof (translation)
The claim follows from `class_exponential`.
-/
theorem classExp : ClassExp := class_exponential
/- English proof (translation)
The claim follows from `RescaleExact_of valTable expIntegral`.
-/
theorem rescaleExact : RescaleExact := RescaleExact_of valTable expIntegral
/- English proof (translation)
The claim follows from `RescaleCore_of rescaleExact classExp classMul`.
-/
theorem rescaleCore : RescaleCore := RescaleCore_of rescaleExact classExp classMul

/- English proof (translation)
The claim follows from `dwork_multivariable`.
-/
theorem dworkMv : DworkMv := dwork_multivariable
/- English proof (translation)
The claim follows from `equivalence_rules`.
-/
theorem simeqRules : SimeqRules := equivalence_rules
/- English proof (translation)
The claim follows from `log_rescale_alt`.
-/
theorem logRescale : LogRescale := log_rescale_alt
/- English proof (translation)
The claim follows from `log_rescale_unique`.
-/
theorem logRescaleUnique : LogRescaleUnique := log_rescale_unique
/- English proof (translation)
The claim follows from `trace_duality`.
-/
theorem traceDual : TraceDual := trace_duality
/- English proof (translation)
The claim follows from `two_sums`.
-/
theorem twoSums : TwoSums := two_sums
/- English proof (translation)
The claim follows from `ThmSCore_of rescaleCore classSubst classChange classMul twoSums logRescale logRescaleUnique`.
-/
theorem thmSCore : ThmSCore :=
  ThmSCore_of rescaleCore classSubst classChange classMul twoSums logRescale logRescaleUnique
/- English proof (translation)
The claim follows from `theorem_s_from_k_one_of thmSCore simeqRules`.
-/
theorem theorem_s_from_k_one : CyclicPowerClassOfExpEquiv := theorem_s_from_k_one_of thmSCore simeqRules

/- English proof (translation)
The claim follows from `formal_law_exists`.
-/
theorem lawExists : LawExists := formal_law_exists
/- English proof (translation)
The claim follows from `formal_law_symmetric`.
-/
theorem lawSymm : LawSymm := formal_law_symmetric
/- English proof (translation)
The claim follows from `divided_derivative`.
-/
theorem divDeriv : DivDeriv := divided_derivative
/- English proof (translation)
The claim follows from `DeIntegral_of divDeriv lawSymm`.
-/
theorem deIntegral : DeIntegral := DeIntegral_of divDeriv lawSymm
/- English proof (translation)
The claim follows from `derivative_a`.
-/
theorem derivA : DerivA := derivative_a
/- English proof (translation)
The claim follows from `LemmaOne_of deIntegral lawSymm`.
-/
theorem lemmaOne : LemmaOne := LemmaOne_of deIntegral lawSymm
/- English proof (translation)
The claim follows from `LemmaTwo_of lemmaOne lawSymm`.
-/
theorem lemmaTwo : LemmaTwo := LemmaTwo_of lemmaOne lawSymm
/- English proof (translation)
The claim follows from `LamModule_of dworkMv`.
-/
theorem lamModule : LamModule := LamModule_of dworkMv
/- English proof (translation)
The claim follows from `StepZero_of lamModule simeqRules lawSymm`.
-/
theorem zeroCondition : StepZero := StepZero_of lamModule simeqRules lawSymm
/- English proof (translation)
The claim follows from `FirstDeriv_of lawSymm`.
-/
theorem firstDeriv : FirstDeriv := FirstDeriv_of lawSymm
/- English proof (translation)
The claim follows from `CobLin_of lawSymm`.
-/
theorem cobLin : CobLin := CobLin_of lawSymm
/- English proof (translation)
The claim follows from `StepI_of lemmaOne firstDeriv cobLin`.
-/
theorem stepI : StepI := StepI_of lemmaOne firstDeriv cobLin
/- English proof (translation)
The claim follows from `StepII_of dworkMv divDeriv deIntegral lawSymm`.
-/
theorem stepII : StepII := StepII_of dworkMv divDeriv deIntegral lawSymm
/- English proof (translation)
The claim follows from `swap_rules`.
-/
theorem swapRules : SwapRules := swap_rules
/- English proof (translation)
The claim follows from `StepH_of lemmaTwo swapRules lawSymm`.
-/
theorem stepH : StepH := StepH_of lemmaTwo swapRules lawSymm
/- English proof (translation)
The claim follows from `c_add_sigma_c_eq_zero`.
-/
theorem stepIII : StepIII := c_add_sigma_c_eq_zero
/- English proof (translation)
The claim follows from `StepIV_of dworkMv`.
-/
theorem stepIV : StepIV := StepIV_of dworkMv
/- English proof (translation)
The claim follows from `mapSimeq_statement`.
-/
theorem mapSimeq : MapSimeq := mapSimeq_statement
/- English proof (translation)
The claim follows from `BetaIsG_of zeroCondition stepI stepII stepH stepIII stepIV swapRules simeqRules`.
-/
theorem betaIsG : BetaIsG :=
  BetaIsG_of zeroCondition stepI stepII stepH stepIII stepIV swapRules simeqRules
/- English proof (translation)
The claim follows from `ThmSFull_of betaIsG theorem_s_from_k_one mapSimeq`.
-/
theorem thmSFull : ThmSFull := ThmSFull_of betaIsG theorem_s_from_k_one mapSimeq

end Formalism.InvariantFactorPaths.G7.Top
