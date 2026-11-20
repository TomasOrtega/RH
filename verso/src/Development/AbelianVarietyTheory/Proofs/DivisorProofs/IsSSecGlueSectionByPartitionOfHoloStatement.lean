import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSSecGlueSectionByPartitionOfHolo
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsSSecGlueSectionByPartitionOfHolo.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.isSSec_glueSectionByPartition_of_holo : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ), (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → A.IsSSec (A.kap + la) (glue C la u) := by
  first | exact @GlobalTheory.OTY.glue_isSSec_of_holo | exact GlobalTheory.OTY.glue_isSSec_of_holo | (intros; apply GlobalTheory.OTY.glue_isSSec_of_holo <;> assumption)
