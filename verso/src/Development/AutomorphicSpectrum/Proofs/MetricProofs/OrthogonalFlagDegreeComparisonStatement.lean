import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OrthogonalFlagDegreeComparison
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FOrthogonalFlagDegreeComparison.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.orthogonal_flag_degree_comparison : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (Ψ : Type) [Fintype Ψ] (j k : ℕ) (A : FlagPair E Ψ j k), A.IsOrthFull → -E.normDegree ⊤ - ∑ τ, A.flatDeg τ ≤ 2 * ∑ τ, -E.normDegree (A.W τ).top ∧ ∀ d : ℤ, d ≠ 0 → (∀ x : E.carrier, d • x ∈ ⨆ a, A.part a) → 2 * ∑ τ, -E.normDegree (A.W τ).top ≤ -E.normDegree ⊤ - ∑ τ, A.flatDeg τ + Module.finrank (𝓞 K) E.carrier * Real.log |(d : ℝ)| := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagPair.two_sum_neg_degree_W | exact GlobalTheory.CompanionTheory.Ar.FlagPair.two_sum_neg_degree_W | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagPair.two_sum_neg_degree_W <;> assumption)
