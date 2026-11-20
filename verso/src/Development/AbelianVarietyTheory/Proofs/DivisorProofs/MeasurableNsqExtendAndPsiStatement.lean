import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableNsqExtendAndPsi
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OTY.measurable_nsq_extend_and_psi` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMeasurableNsqExtendAndPsi.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.measurable_nsq_and_psi_of_isSecOn : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (Ω : Set Y) (h : ι → Y → ℂ), IsOpen Ω → A.IsSecOn la Ω h → (∀ i y, y ∉ Ω → h i y = 0) → Measurable (A.nsq la h) ∧ ∀ (L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → Measurable (psi A L s) := by
  first | exact @GlobalTheory.OTY.measurable_nsq_extend_and_psi | exact GlobalTheory.OTY.measurable_nsq_extend_and_psi | (intros; apply GlobalTheory.OTY.measurable_nsq_extend_and_psi <;> assumption)
