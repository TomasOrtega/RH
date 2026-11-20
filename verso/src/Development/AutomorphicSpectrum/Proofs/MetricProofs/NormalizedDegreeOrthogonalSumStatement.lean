import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeOrthogonalSum
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.OrthSum.normDegree_rank_iSup` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FNormalizedDegreeOrthogonalSum.lean&line=144#L144)
-/
theorem _root_.GlobalTheory.T.normalized_degree_orthogonal_sum : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (I : Type) [Fintype I] (F : I → Submodule (𝓞 K) E.carrier), (∀ a b, a ≠ b → OrthAt E (F a) (F b)) → E.normDegree (⨆ a, F a) = ∑ a, E.normDegree (F a) ∧ E.rank (⨆ a, F a) = ∑ a, E.rank (F a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrthSum.normDegree_rank_iSup | exact GlobalTheory.CompanionTheory.Ar.OrthSum.normDegree_rank_iSup | (intros; apply GlobalTheory.CompanionTheory.Ar.OrthSum.normDegree_rank_iSup <;> assumption)
