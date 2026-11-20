import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorPowFractionalIdealNonarchSize
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_generator_pow_fractional_size` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsGeneratorPowFractionalIdealNonarchSize.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.exists_generator_pow_fractionalIdeal_nonarch_size : ∀ (K : Type) [Field K] [NumberField K] (I : Submodule (𝓞 K) K), I ≠ ⊥ → (∃ n : ℕ, 0 < n ∧ ∀ x ∈ I, (n : K) * x ∈ (algebraMap (𝓞 K) K).range) → ∃ (h : ℕ) (α : K), 0 < h ∧ α ≠ 0 ∧ ∀ v : K →*₀ ℝ, (∀ x, 0 ≤ v x) → (∀ x y, v (x + y) ≤ max (v x) (v y)) → (∀ c : 𝓞 K, v (c : K) ≤ 1) → ∀ x₀ ∈ I, (∀ x ∈ I, v x ≤ v x₀) → v α = v x₀ ^ h := by
  first | exact @GlobalTheory.exists_generator_pow_fractional_size | exact GlobalTheory.exists_generator_pow_fractional_size | (intros; apply GlobalTheory.exists_generator_pow_fractional_size <;> assumption)
