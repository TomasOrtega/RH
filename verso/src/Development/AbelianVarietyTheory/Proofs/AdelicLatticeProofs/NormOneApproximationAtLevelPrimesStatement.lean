import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormOneApproximationAtLevelPrimes
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnRep.normOne_approx` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FNormOneApproximationAtLevelPrimes.lean&line=178#L178)
-/
theorem _root_.GlobalTheory.T.normOne_approximation_at_level_primes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), (∀ x, c (c x) = x) → c ≠ 1 → ∀ (u : E) (N D : ℕ), u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ (∃ t : ℕ, t.Coprime N ∧ ∃ b : 𝓞 E, (t : E) * (u' / u - 1) = (D : E) * (b : E)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ (∃ b : 𝓞 E, (s : E) * (u' - 1) = (D : E) * (b : E)) ∧ ∃ b : 𝓞 E, (s : E) * (u'⁻¹ - 1) = (D : E) * (b : E) := by
  first | exact @GlobalTheory.UnRep.normOne_approx | exact GlobalTheory.UnRep.normOne_approx | (intros; apply GlobalTheory.UnRep.normOne_approx <;> assumption)
