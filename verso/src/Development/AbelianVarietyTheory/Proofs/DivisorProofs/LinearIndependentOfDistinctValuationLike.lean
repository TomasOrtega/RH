import Mathlib

open Filter Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `C V Γ ι _ _ _ _ ν hsm hadd f hf hinj`. Establish `key : ∀ (g : ι → C) (s : Finset ι), s.Nonempty → (∀ i ∈ s, g i ≠ 0) → (∑ i ∈ s, g i • f i) ≠ 0 ∧ ∃ j ∈ s, ν (∑ i ∈ s, g i • f i) = ν (f j)`. Introduce `g s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro h`.

Conclude with `absurd h Finset.not_nonempty_empty`. Consider the case `@insert a s ha ih`. Introduce `_ hg`. Establish `hga : g a ≠ 0` using `hg a (Finset.mem_insert_self a s)`. Establish `hx : g a • f a ≠ 0` using `smul_ne_zero hga (hf a)`.

Establish `hνx : ν (g a • f a) = ν (f a)` using `hsm _ _ hga`. Rewrite using `[Finset.sum_insert ha]`. Break down `s.eq_empty_or_nonempty with hs | hs` into its components or cases. Substitute `hs` using the available equality. Simplify using `only [Finset.sum_empty, add_zero]`.

Conclude with `⟨hx, a, Finset.mem_insert_self a _, hνx⟩`. Take `⟨hy, j, hj, hνy⟩` from `ih hs (fun i hi => hg i (Finset.mem_insert_of_mem hi))`. Establish `hne : ν (f a) ≠ ν (f j)`. Introduce `h`. Establish `: a = j` using `hinj h`.

Conclude with `ha (this ▸ hj)`. Break down `lt_or_gt_of_ne hne with hlt | hlt` into its components or cases. Take `⟨h1, h2⟩` from `hadd _ _ hx hy (by rw [hνx, hνy]; exact hlt)`. Conclude with `⟨h1, a, Finset.mem_insert_self a s, by rw [h2, hνx]⟩`. Take `⟨h1, h2⟩` from `hadd _ _ hy hx (by rw [hνx, hνy]; exact hlt)`.

Use `⟨by rw [add_comm]; exact h1, j, Finset.mem_insert_of_mem hj, ?_⟩` and prove the remaining obligations. Rewrite using `[add_comm, h2, hνy]`. Rewrite using `[linearIndependent_iff']`. Introduce `s g hsum i hi`. Assume the negation of the conclusion as `hgi`.

Establish `hsum' : ∑ k ∈ s.filter (fun k => g k ≠ 0), g k • f k = 0`. Rewrite using `[Finset.sum_filter_of_ne]`. Conclude with `hsum`. Introduce `x _ hx h`. Apply `hx` to reduce the goal to its premises.

Simplify using `[h]`. Establish `hne : (s.filter (fun k => g k ≠ 0)).Nonempty` using `⟨i, Finset.mem_filter.2 ⟨hi, hgi⟩⟩`. Conclude with `(key g _ hne (fun j hj => (Finset.mem_filter.1 hj).2)).1 hsum'`.
-/
theorem linearIndependent_of_distinct_valuationLike :
    ∀ (C V Γ ι : Type) [Field C] [AddCommGroup V] [Module C V] [LinearOrder Γ] (ν : V → Γ),
      (∀ (c : C) (u : V), c ≠ 0 → ν (c • u) = ν u) →
      (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u < ν v → u + v ≠ 0 ∧ ν (u + v) = ν u) →
      ∀ f : ι → V, (∀ i, f i ≠ 0) → Function.Injective (fun i => ν (f i)) →
        LinearIndependent C f := by
  intro C V Γ ι _ _ _ _ ν hsm hadd f hf hinj
  classical
  have key : ∀ (g : ι → C) (s : Finset ι), s.Nonempty → (∀ i ∈ s, g i ≠ 0) →
      (∑ i ∈ s, g i • f i) ≠ 0 ∧ ∃ j ∈ s, ν (∑ i ∈ s, g i • f i) = ν (f j) := by
    intro g s
    induction s using Finset.induction_on with
    | empty => intro h; exact absurd h Finset.not_nonempty_empty
    | @insert a s ha ih =>
      intro _ hg
      have hga : g a ≠ 0 := hg a (Finset.mem_insert_self a s)
      have hx : g a • f a ≠ 0 := smul_ne_zero hga (hf a)
      have hνx : ν (g a • f a) = ν (f a) := hsm _ _ hga
      rw [Finset.sum_insert ha]
      rcases s.eq_empty_or_nonempty with hs | hs
      · subst hs
        simp only [Finset.sum_empty, add_zero]
        exact ⟨hx, a, Finset.mem_insert_self a _, hνx⟩
      · obtain ⟨hy, j, hj, hνy⟩ := ih hs (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        have hne : ν (f a) ≠ ν (f j) := by
          intro h
          have : a = j := hinj h
          exact ha (this ▸ hj)
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · obtain ⟨h1, h2⟩ := hadd _ _ hx hy (by rw [hνx, hνy]; exact hlt)
          exact ⟨h1, a, Finset.mem_insert_self a s, by rw [h2, hνx]⟩
        · obtain ⟨h1, h2⟩ := hadd _ _ hy hx (by rw [hνx, hνy]; exact hlt)
          refine ⟨by rw [add_comm]; exact h1, j, Finset.mem_insert_of_mem hj, ?_⟩
          rw [add_comm, h2, hνy]
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  have hsum' : ∑ k ∈ s.filter (fun k => g k ≠ 0), g k • f k = 0 := by
    rw [Finset.sum_filter_of_ne]
    · exact hsum
    · intro x _ hx h
      apply hx
      simp [h]
  have hne : (s.filter (fun k => g k ≠ 0)).Nonempty := ⟨i, Finset.mem_filter.2 ⟨hi, hgi⟩⟩
  exact (key g _ hne (fun j hj => (Finset.mem_filter.1 hj).2)).1 hsum'

end GlobalTheory
