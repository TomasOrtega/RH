import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSlowlyIncreasing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRealLieSmoothingMemSlowlyIncreasing.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.realLieSmoothing_mem_slowlyIncreasing : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ f ∈ growth E a, smoothing ν α f ∈ growth E a := by
  first | exact @GlobalTheory.AutGrowth.smoothing_mem_growth | exact GlobalTheory.AutGrowth.smoothing_mem_growth | (intros; apply GlobalTheory.AutGrowth.smoothing_mem_growth <;> assumption)
