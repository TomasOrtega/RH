import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuationOfGeneratorOfPow
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FValuationOfGeneratorOfPow.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.valuation_eq_exp_neg_of_pow_eq_span_singleton : ∀ (K : Type) [Field K] [NumberField K] (𝔭 : HeightOneSpectrum (𝓞 K)) (n : ℕ) (π : 𝓞 K), 𝔭.asIdeal ^ n = Ideal.span {π} → 𝔭.valuation K (π : K) = WithZero.exp (-(n : ℤ)) := by
  first | exact @GlobalTheory.valuation_of_generator_of_pow | exact GlobalTheory.valuation_of_generator_of_pow | (intros; apply GlobalTheory.valuation_of_generator_of_pow <;> assumption)
