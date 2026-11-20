import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpLiftL2DiscreteQuotientOnCompact
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
open MeasureTheory GlobalTheory.AutomorphicL2Unitary
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AutomorphicL2Local.memLp_restrict_compact` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FMemLpLiftL2DiscreteQuotientOnCompact.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.memLp_lift_L2DiscreteQuotient_on_compact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ (F : L2 Γ μ) (C : Set G), IsCompact C → MemLp (lift Γ F) 2 (μ.restrict C) ∧ IntegrableOn (lift Γ F) C μ := by
  first | exact @GlobalTheory.AutomorphicL2Local.memLp_restrict_compact | exact GlobalTheory.AutomorphicL2Local.memLp_restrict_compact | (intros; apply GlobalTheory.AutomorphicL2Local.memLp_restrict_compact <;> assumption)
