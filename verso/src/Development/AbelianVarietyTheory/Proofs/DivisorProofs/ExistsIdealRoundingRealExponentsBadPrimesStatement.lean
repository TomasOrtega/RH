import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealRoundingRealExponentsBadPrimes
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Rounding.exists_rounding` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIdealRoundingRealExponentsBadPrimes.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.exists_ideal_rounding_realExponents_badPrimes : ∀ (K : Type) [Field K] [NumberField K] (B : Finset ℕ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ), (∀ p ∈ B, p.Prime) → (Function.support ρ).Finite → (∀ w : HeightOneSpectrum (𝓞 K), (∀ p ∈ B, ((p : ℕ) : 𝓞 K) ∉ w.asIdeal) → ∃ n : ℤ, ρ w = n) → ∃ (a : K) (𝔞 : Ideal (𝓞 K)), a ≠ 0 ∧ 𝔞 ≠ ⊥ ∧ (∀ b ∈ 𝔞, b ≠ 0 → ∀ w, 0 ≤ (vAdd w ((b : K) * a) : ℝ) + ρ w) ∧ (∑ᶠ w, ρ w * lw K w) - ∑ p ∈ B, Real.log p ≤ -((∑ σ : K →+* ℂ, Real.log ‖σ a‖) / (Module.finrank ℚ K : ℝ)) - Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ) := by
  first | exact @GlobalTheory.Rounding.exists_rounding | exact GlobalTheory.Rounding.exists_rounding | (intros; apply GlobalTheory.Rounding.exists_rounding <;> assumption)
