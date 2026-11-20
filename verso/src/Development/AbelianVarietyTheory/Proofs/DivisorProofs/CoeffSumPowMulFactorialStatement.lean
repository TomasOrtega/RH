import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSumPowMulFactorial
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WinSet
open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm GlobalTheory.FlagCurve Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MultinomCoeff.coeff_mono_sum_pow_mul` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoeffSumPowMulFactorial.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.coeff_sum_pow_mul_factorial : ∀ {σ : Type} [DecidableEq σ] (C R : Finset σ) (k : ℕ) (ω : MvPolynomial σ ℝ), coeff (mono R) ((∑ s ∈ C, X s) ^ k * ω) = (k.factorial : ℝ) * ∑ U ∈ (R ∩ C).powersetCard k, coeff (mono (R \ U)) ω := by
  first | exact @GlobalTheory.MultinomCoeff.coeff_mono_sum_pow_mul | exact GlobalTheory.MultinomCoeff.coeff_mono_sum_pow_mul | (intros; apply GlobalTheory.MultinomCoeff.coeff_mono_sum_pow_mul <;> assumption)
