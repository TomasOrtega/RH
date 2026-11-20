import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactUnipotentInCompactSubgroup

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.UnipExhaust

/- English proof (translation)
Introduce `k _ _ _ _ N s hs`. Take `⟨U₀, hU, hsU⟩` from `GlobalTheory.UnipCptSub.exists_compact_subgroup_of_isCompact (↑s : Set (GL (Fin N) k)) s.finite_toSet.isCompact hs`. Establish `hcl : IsClosed (unipB k (Fin N) : Set (GL (Fin N) k))`. Rewrite using `[GlobalTheory.UnipCptSub.unipB_eq_unipOf]`. Conclude with `GlobalTheory.UnipCompact.isClosed_unipOf _`.

Use `⟨U₀ ⊓ unipB k (Fin N), inf_le_right, fun g hg => ⟨hsU hg, hs hg⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_inf]`. Conclude with `hU.inter_right hcl`.
-/
theorem exists_compact_subgroup_of_finset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ)
      (s : Finset (GL (Fin N) k)), (↑s : Set (GL (Fin N) k)) ⊆ unipB k (Fin N) →
      ∃ L : Subgroup (GL (Fin N) k), L ≤ unipB k (Fin N) ∧ (↑s : Set (GL (Fin N) k)) ⊆ L ∧
        IsCompact (L : Set (GL (Fin N) k)) := by
  intro k _ _ _ _ N s hs
  obtain ⟨U₀, hU, hsU⟩ := GlobalTheory.UnipCptSub.exists_compact_subgroup_of_isCompact
    (↑s : Set (GL (Fin N) k)) s.finite_toSet.isCompact hs
  have hcl : IsClosed (unipB k (Fin N) : Set (GL (Fin N) k)) := by
    rw [GlobalTheory.UnipCptSub.unipB_eq_unipOf]
    exact GlobalTheory.UnipCompact.isClosed_unipOf _
  refine ⟨U₀ ⊓ unipB k (Fin N), inf_le_right, fun g hg => ⟨hsU hg, hs hg⟩, ?_⟩
  rw [Subgroup.coe_inf]
  exact hU.inter_right hcl

end GlobalTheory.CompanionTheory.UnipExhaust
