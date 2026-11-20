import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ExtensionAcrossDenseNonvanishing
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FL2ExtensionAcrossDenseNonvanishing.lean&line=158#L158)
-/
theorem _root_.GlobalTheory.T.exists_isSec_extension_of_dense_nz_of_l2 : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ la : La) (τ F : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → A.IsSecOn la (nz A τ) F → ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq la F y) ∂A.mu < ⊤ → ∃ G : ι → Y → ℂ, A.IsSec la G ∧ ∀ i y, y ∈ nz A τ → y ∈ (A.chart i).source → G i y = F i y := by
  first | exact @GlobalTheory.OTY.l2_extension_nz | exact GlobalTheory.OTY.l2_extension_nz | (intros; apply GlobalTheory.OTY.l2_extension_nz <;> assumption)
