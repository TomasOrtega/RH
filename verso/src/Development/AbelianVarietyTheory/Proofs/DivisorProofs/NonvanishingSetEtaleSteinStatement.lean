import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingSetEtaleStein
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.nzEtaleStein` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNonvanishingSetEtaleStein.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.nonvanishingSet_etale_stein : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n), A.IsSec Λ τ → A.Pos Λ (fun _ => 0) → Etale A (nz A τ) z → ∃ X : EtaleStein n (nz A τ), X.z = (fun y : nz A τ => z y) ∧ X.e = fun y : nz A τ => -Real.log (A.nsq Λ τ y) := by
  first | exact @GlobalTheory.nzEtaleStein | exact GlobalTheory.nzEtaleStein | (intros; apply GlobalTheory.nzEtaleStein <;> assumption)
