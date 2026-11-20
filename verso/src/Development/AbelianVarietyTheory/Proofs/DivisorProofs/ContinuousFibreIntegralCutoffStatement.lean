import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFibreIntegralCutoff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppendVMemFamAtlasTarget
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real Topology

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BcUnique.continuous_integral_fib` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContinuousFibreIntegralCutoff.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.continuous_fibre_integral_cutoff : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (A : HolAtlas M 1) (α : (famAtlas A).Fld), (famAtlas A).IsForm α → ∀ (χ : M → ℝ) (j : A.ι), A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e j).source → Continuous fun t : OnePoint ℂ => A.integral (A.fn χ * (famAtlas A).pullback A (fib t) α) := by
  first | exact @GlobalTheory.BcUnique.continuous_integral_fib | exact GlobalTheory.BcUnique.continuous_integral_fib | (intros; apply GlobalTheory.BcUnique.continuous_integral_fib <;> assumption)
