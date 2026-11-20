import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationSqrtAbsNormEqOne
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.valuation_sqrt_absNorm_eq_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FValuationSqrtAbsNormEqOne.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.valuation_sqrt_absNorm_eq_one' : ∀ (K : Type) [Field K] [NumberField K] (A : ValuationSubring ℂ) (p : ℕ), p.Prime → (p : ℂ) ∈ A.nonunits → ∀ (P : HeightOneSpectrum (𝓞 K)), (p : 𝓞 K) ∉ P.asIdeal → A.valuation (((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.valuation_sqrt_absNorm_eq_one | exact GlobalTheory.valuation_sqrt_absNorm_eq_one | (intros; apply GlobalTheory.valuation_sqrt_absNorm_eq_one <;> assumption)
