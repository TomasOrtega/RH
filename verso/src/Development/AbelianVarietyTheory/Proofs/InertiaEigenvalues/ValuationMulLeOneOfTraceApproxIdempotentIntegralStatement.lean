import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationMulLeOneOfTraceApproxIdempotentIntegral
import Mathlib
open NumberField IsDedekindDomain
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InvDiffLocal.valuation_mul_different_le_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FValuationMulLeOneOfTraceApproxIdempotentIntegral.lean&line=117#L117)
-/
theorem _root_.GlobalTheory.T.valuation_mul_le_one_of_trace_approxIdempotent_integral : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (la : HeightOneSpectrum (𝓞 L)) (p : HeightOneSpectrum (𝓞 K)), la.asIdeal.under (𝓞 K) = p.asIdeal → ∀ y : L, (∃ N : ℕ, ∀ b : 𝓞 L, (∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la → la'.asIdeal.under (𝓞 K) = p.asIdeal → b ∈ la'.asIdeal ^ N) → p.valuation K (Algebra.trace K L ((b : L) * y)) ≤ 1) → ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), la.valuation L (y * (d : L)) ≤ 1 := by
  first | exact @GlobalTheory.InvDiffLocal.valuation_mul_different_le_one | exact GlobalTheory.InvDiffLocal.valuation_mul_different_le_one | (intros; apply GlobalTheory.InvDiffLocal.valuation_mul_different_le_one <;> assumption)
