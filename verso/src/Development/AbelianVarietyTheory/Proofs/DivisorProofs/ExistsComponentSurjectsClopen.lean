import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `A B _ _ f hf hop hcl hcomp S hS hSc a ha`. Use `⟨irreducibleComponent a, irreducibleComponent_mem_irreducibleComponents a, mem_irreducibleComponent, ?_⟩` and prove the remaining obligations. Establish `hCc : IsClosed (irreducibleComponent a)` using `isClosed_irreducibleComponent`. Establish `hCo : IsOpen (irreducibleComponent a)` using `hcomp _ (irreducibleComponent_mem_irreducibleComponents a)`. Establish `hCp : IsPreconnected (irreducibleComponent a)` using `(IsIrreducible.isConnected (isIrreducible_irreducibleComponent (x := a))).isPreconnected`.

Establish `hsub : irreducibleComponent a ⊆ f ⁻¹' S` using `hCp.subset_isClopen (hS.preimage hf) ⟨a, mem_irreducibleComponent, ha⟩`. Establish `himg : f '' irreducibleComponent a ⊆ S` using `Set.image_subset_iff.mpr hsub`. Establish `hclo : IsClopen (f '' irreducibleComponent a)` using `⟨hcl _ hCc, hop _ hCo⟩`. Use `le_antisymm himg ?_` and prove the remaining obligations. Conclude with `hSc.subset_isClopen hclo ⟨f a, ha, a, mem_irreducibleComponent, rfl⟩`.
-/
theorem clopen_image_irreducibleComponent : ∀ {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : A → B), Continuous f → IsOpenMap f → IsClosedMap f →
    (∀ C ∈ irreducibleComponents A, IsOpen C) → ∀ S : Set B, IsClopen S → IsPreconnected S → ∀ a : A, f a ∈ S →
    ∃ C ∈ irreducibleComponents A, a ∈ C ∧ f '' C = S := by
  intro A B _ _ f hf hop hcl hcomp S hS hSc a ha
  refine ⟨irreducibleComponent a, irreducibleComponent_mem_irreducibleComponents a,
    mem_irreducibleComponent, ?_⟩
  have hCc : IsClosed (irreducibleComponent a) := isClosed_irreducibleComponent
  have hCo : IsOpen (irreducibleComponent a) :=
    hcomp _ (irreducibleComponent_mem_irreducibleComponents a)
  have hCp : IsPreconnected (irreducibleComponent a) :=
    (IsIrreducible.isConnected (isIrreducible_irreducibleComponent (x := a))).isPreconnected
  have hsub : irreducibleComponent a ⊆ f ⁻¹' S :=
    hCp.subset_isClopen (hS.preimage hf) ⟨a, mem_irreducibleComponent, ha⟩
  have himg : f '' irreducibleComponent a ⊆ S := Set.image_subset_iff.mpr hsub
  have hclo : IsClopen (f '' irreducibleComponent a) := ⟨hcl _ hCc, hop _ hCo⟩
  refine le_antisymm himg ?_
  exact hSc.subset_isClopen hclo ⟨f a, ha, a, mem_irreducibleComponent, rfl⟩

end GlobalTheory
