import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupAddSubgroup
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIsCompactSupAddSubgroup.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.isCompact_sup_addSubgroup : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A B : AddSubgroup X), IsCompact (A : Set X) → IsCompact (B : Set X) → IsCompact ((A ⊔ B : AddSubgroup X) : Set X) := by
  first | exact @GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup | exact GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup | (intros; apply GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup <;> assumption)
