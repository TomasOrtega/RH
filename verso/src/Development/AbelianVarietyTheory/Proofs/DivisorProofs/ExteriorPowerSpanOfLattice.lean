import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem GlobalTheory.span_ιMulti_span_range_eq : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (h N : ℕ) (g : Fin h → V), Submodule.span O {w : ⋀[C]^N V | ∃ x : Fin N → V, (∀ i, x i ∈ (Submodule.span O (Set.range g) : Set V)) ∧ w = exteriorPower.ιMulti C N x} = Submodule.span O (Set.range (fun s : Fin N → Fin h => exteriorPower.ιMulti C N (g ∘ s))) := by
  intro C _ O _ _ V _ _ _ _ h N g
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w ⟨x, hx, rfl⟩
    have hc : ∀ i, ∃ c : Fin h → O, ∑ j, c j • g j = x i := fun i =>
      (Submodule.mem_span_range_iff_exists_fun O).1 (hx i)
    choose c hc using hc
    have hx' : x = fun i => ∑ j, (algebraMap O C (c i j)) • g j := by
      funext i; rw [← hc i]; simp [algebraMap_smul]
    rw [hx']
    show (exteriorPower.ιMulti C N).toMultilinearMap (fun i => ∑ j, (algebraMap O C (c i j)) • g j) ∈ _
    rw [MultilinearMap.map_sum]
    refine Submodule.sum_mem _ (fun s _ => ?_)
    rw [MultilinearMap.map_smul_univ, ← map_prod, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · apply Submodule.span_mono
    rintro w ⟨s, rfl⟩
    exact ⟨g ∘ s, fun i => Submodule.subset_span ⟨s i, rfl⟩, rfl⟩
