import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDetIsFrameOnCanonicalWeight
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OTY.jdet_isFrameOn_kap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FJacobianDetIsFrameOnCanonicalWeight.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.jacobianDet_isFrameOn_canonicalWeight : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → A.IsFrameOn A.kap U (jdet A z) := by
  first | exact @GlobalTheory.OTY.jdet_isFrameOn_kap | exact GlobalTheory.OTY.jdet_isFrameOn_kap | (intros; apply GlobalTheory.OTY.jdet_isFrameOn_kap <;> assumption)
