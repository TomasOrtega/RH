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
A detailed English derivation is pending.
-/
theorem expSpec : ExpSpec := exponential_specification
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frobSq : FrobSq := frobenius_square
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ipLemma : IPLemma := integral_part_lemma
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ipClosure : IPClosure := integral_part_closure
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem teichSigma : TeichSigma := teichmuller_sigma
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mulSpec : MulSpec := MulSpec_of expSpec ipLemma ipClosure
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem betaHypOfF : BetaHypOfF := BetaHypOfF_of teichSigma
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem letterShift : LetterShift := letter_shift
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem shiftIP : ShiftIP := ShiftIP_of_frobSq frobSq
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem substTil : SubstTil := subst_tilde
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pairRules : PairRules := PairRules_of expSpec ipLemma
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem torusTil : TorusTil := torus_tilde
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mean_second_biextension_condition : MeanTorusInvariant := second_mean_condition
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mean_third_biextension_condition : MeanNoLowBidegreeTerms := third_mean_condition
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem torus_sum_coboundary_condition : TorusSumCoboundaryCondition := fourth_condition_of_pairing_rules pairRules substTil shiftIP letterShift
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem biextension_hypotheses_of_level_one : MeanBiextensionHypothesesOfCocycle := biextension_hypotheses_of_conditions torus_sum_coboundary_condition torusTil teichSigma mean_second_biextension_condition mean_third_biextension_condition
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dualExpand : DualExpand := dual_expansion
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tilInvariantL : TilInvariantL := TilInvariantL_of pairRules substTil torusTil teichSigma shiftIP ipClosure dualExpand frobSq
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem meanSimeqL : MeanSimeqL := MeanSimeqL_of tilInvariantL
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem beTilXY : BeTilXY := BeTilXY_of expSpec
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bMinus1 : BMinus1 := BMinus1_of' expSpec
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem meanSimeq : MeanSimeq := MeanSimeq_of' meanSimeqL beTilXY letterShift
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem biextension_points_integral : BiextensionPointsIntegral := biextension_points_of_exp_spec expSpec meanSimeqL
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem b0 : B0 := biextension_of_exp_spec expSpec biextension_points_integral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oneLetterHalf : OneLetterHalf := OneLetterHalf_of meanSimeqL
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem single_letter_theta_factorization : SingleLetterThetaFactorization := single_letter_of_half oneLetterHalf

end Formalism.L2.Th1.D
