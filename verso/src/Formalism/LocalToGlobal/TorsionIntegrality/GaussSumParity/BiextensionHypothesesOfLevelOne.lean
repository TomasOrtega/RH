import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ExponentialSpecification
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.IpNormPowSubPowLe
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.EqZeroOfPowEqOne
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SubstFirstCoboundaryThree
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SubstZeroOfConstantCoeff
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionHypothesesOfConditions
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.TilInvariantLOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.FirstMomentIdempotentLaw
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionOfExpSpec
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.AtVariableArtinHasseEqOneLog

namespace Formalism.L2.Th1.D

/- English proof (translation)
The claim follows from `exponential_specification`.
-/
theorem expSpec : ExpSpec := exponential_specification
/- English proof (translation)
The claim follows from `frobenius_square`.
-/
theorem frobSq : FrobSq := frobenius_square
/- English proof (translation)
The claim follows from `integral_part_lemma`.
-/
theorem ipLemma : IPLemma := integral_part_lemma
/- English proof (translation)
The claim follows from `integral_part_closure`.
-/
theorem ipClosure : IPClosure := integral_part_closure
/- English proof (translation)
The claim follows from `teichmuller_sigma`.
-/
theorem teichSigma : TeichSigma := teichmuller_sigma
/- English proof (translation)
The claim follows from `MulSpec_of expSpec ipLemma ipClosure`.
-/
theorem mulSpec : MulSpec := MulSpec_of expSpec ipLemma ipClosure
/- English proof (translation)
The claim follows from `BetaHypOfF_of teichSigma`.
-/
theorem betaHypOfF : BetaHypOfF := BetaHypOfF_of teichSigma
/- English proof (translation)
The claim follows from `letter_shift`.
-/
theorem letterShift : LetterShift := letter_shift
/- English proof (translation)
The claim follows from `ShiftIP_of_frobSq frobSq`.
-/
theorem shiftIP : ShiftIP := ShiftIP_of_frobSq frobSq
/- English proof (translation)
The claim follows from `subst_tilde`.
-/
theorem substTil : SubstTil := subst_tilde
/- English proof (translation)
The claim follows from `PairRules_of expSpec ipLemma`.
-/
theorem pairRules : PairRules := PairRules_of expSpec ipLemma
/- English proof (translation)
The claim follows from `torus_tilde`.
-/
theorem torusTil : TorusTil := torus_tilde
/- English proof (translation)
The claim follows from `second_mean_condition`.
-/
theorem mean_second_biextension_condition : MeanTorusInvariant := second_mean_condition
/- English proof (translation)
The claim follows from `third_mean_condition`.
-/
theorem mean_third_biextension_condition : MeanNoLowBidegreeTerms := third_mean_condition
/- English proof (translation)
The claim follows from `fourth_condition_of_pairing_rules pairRules substTil shiftIP letterShift`.
-/
theorem torus_sum_coboundary_condition : TorusSumCoboundaryCondition := fourth_condition_of_pairing_rules pairRules substTil shiftIP letterShift
/- English proof (translation)
The claim follows from `biextension_hypotheses_of_conditions torus_sum_coboundary_condition torusTil teichSigma mean_second_biextension_condition mean_third_biextension_condition`.
-/
theorem biextension_hypotheses_of_level_one : MeanBiextensionHypothesesOfCocycle := biextension_hypotheses_of_conditions torus_sum_coboundary_condition torusTil teichSigma mean_second_biextension_condition mean_third_biextension_condition
/- English proof (translation)
The claim follows from `dual_expansion`.
-/
theorem dualExpand : DualExpand := dual_expansion
/- English proof (translation)
The claim follows from `TilInvariantL_of pairRules substTil torusTil teichSigma shiftIP ipClosure dualExpand frobSq`.
-/
theorem tilInvariantL : TilInvariantL := TilInvariantL_of pairRules substTil torusTil teichSigma shiftIP ipClosure dualExpand frobSq
/- English proof (translation)
The claim follows from `MeanSimeqL_of tilInvariantL`.
-/
theorem meanSimeqL : MeanSimeqL := MeanSimeqL_of tilInvariantL
/- English proof (translation)
The claim follows from `BeTilXY_of expSpec`.
-/
theorem beTilXY : BeTilXY := BeTilXY_of expSpec
/- English proof (translation)
The claim follows from `BMinus1_of' expSpec`.
-/
theorem bMinus1 : BMinus1 := BMinus1_of' expSpec
/- English proof (translation)
The claim follows from `MeanSimeq_of' meanSimeqL beTilXY letterShift`.
-/
theorem meanSimeq : MeanSimeq := MeanSimeq_of' meanSimeqL beTilXY letterShift
/- English proof (translation)
The claim follows from `biextension_points_of_exp_spec expSpec meanSimeqL`.
-/
theorem biextension_points_integral : BiextensionPointsIntegral := biextension_points_of_exp_spec expSpec meanSimeqL
/- English proof (translation)
The claim follows from `biextension_of_exp_spec expSpec biextension_points_integral`.
-/
theorem b0 : B0 := biextension_of_exp_spec expSpec biextension_points_integral
/- English proof (translation)
The claim follows from `OneLetterHalf_of meanSimeqL`.
-/
theorem oneLetterHalf : OneLetterHalf := OneLetterHalf_of meanSimeqL
/- English proof (translation)
The claim follows from `single_letter_of_half oneLetterHalf`.
-/
theorem single_letter_theta_factorization : SingleLetterThetaFactorization := single_letter_of_half oneLetterHalf

end Formalism.L2.Th1.D
