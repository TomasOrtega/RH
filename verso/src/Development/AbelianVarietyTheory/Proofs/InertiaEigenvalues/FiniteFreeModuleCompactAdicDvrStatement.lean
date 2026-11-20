import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFreeModuleCompactAdicDvr
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.finite_free_compact_adic_dvr` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteFreeModuleCompactAdicDvr.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.finite_free_module_compact_adic_dvr : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul O M] [T2Space M] [Module.Free O M] [Module.Finite O M] (ϖ : O), Irreducible ϖ → CompactSpace M ∧ IsOpen (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) ∧ Topology.IsClosedEmbedding (fun m : M => ϖ • m) := by
  first | exact @GlobalTheory.finite_free_compact_adic_dvr | exact GlobalTheory.finite_free_compact_adic_dvr | (intros; apply GlobalTheory.finite_free_compact_adic_dvr <;> assumption)
