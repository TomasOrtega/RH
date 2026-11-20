import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFormDefiningValue
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Small.exists_form_hasVal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FExistsFormDefiningValue.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_form_defining_value : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω), Birational y → IsRelevant (mCoordIdeal y) → ∀ (a : K → ℤ) (s : Ω), ∃ h : MRing ι, IsFormOff (mCoordIdeal y) h ∧ ∀ (𝕜 : Type) [Field 𝕜] (z : (Σ k, ι k) → 𝕜), aeval z h ≠ 0 → ∃ w, HasVal y a s z w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.exists_form_hasVal | exact GlobalTheory.CompanionTheory.Ar.Small.exists_form_hasVal | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.exists_form_hasVal <;> assumption)
