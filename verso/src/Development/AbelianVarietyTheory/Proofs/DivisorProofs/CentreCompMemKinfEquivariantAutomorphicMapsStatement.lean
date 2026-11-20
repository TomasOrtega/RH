import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompMemKinfEquivariantAutomorphicMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AutGrowth.comp_mem_maps` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCentreCompMemKinfEquivariantAutomorphicMaps.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.centre_comp_mem_kinfEquivariantAutomorphicMaps : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W) (T : W →ₗ[ℂ] Sm E a), T ∈ maps L W hW → ∀ z ∈ Zalg E a, z ∘ₗ T ∈ maps L W hW := by
  first | exact @GlobalTheory.AutGrowth.comp_mem_maps | exact GlobalTheory.AutGrowth.comp_mem_maps | (intros; apply GlobalTheory.AutGrowth.comp_mem_maps <;> assumption)
