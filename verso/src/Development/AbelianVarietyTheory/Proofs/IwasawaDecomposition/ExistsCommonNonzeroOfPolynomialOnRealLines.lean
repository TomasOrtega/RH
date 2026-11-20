import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `_` using `Fintype.ofFinite ι`. Establish `key : ∀ t : Finset ι, ∃ v, ∀ i ∈ t, f i v ≠ 0`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => exact ⟨0, by simp⟩`.

Consider the case `insert j t hj ih`. Take `⟨v, hv⟩` from `ih`. Take `⟨w, hw⟩` from `hne j`. Use `choose p hp using fun i => hpoly i v (w - v)`. Establish `hp0 : ∀ i ∈ insert j t, p i ≠ 0`.

Introduce `i hi h`. Break down `Finset.mem_insert.1 hi with hij | hi` into its components or cases. Substitute `hij` using the available equality. Apply `hw` to reduce the goal to its premises. Use `hp i 1` as an intermediate fact.

Simplify `this` using `[h]`. Apply `hv i hi` to reduce the goal to its premises. Use `hp i 0` as an intermediate fact. Simplify `this` using `[h]`. Establish `hfin : Set.Finite (⋃ i ∈ (insert j t : Finset ι), (fun s : ℝ => (s : ℂ)) ⁻¹' {z | (p i).IsRoot z})` using `Set.Finite.biUnion (Finset.finite_toSet _) fun i hi => (Polynomial.finite_setOf_isRoot (hp0 i hi)).preimage Complex.ofReal_injective.injOn`.

Take `⟨s, hs⟩` from `hfin.exists_notMem`. Use `⟨v + s • (w - v), fun i hi => ?_⟩` and prove the remaining obligations. Rewrite using `[hp i s]`. Introduce `h0`. Apply `hs` to reduce the goal to its premises.

Simplify using `only [Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq]`. Conclude with `⟨i, hi, h0⟩`. Take `⟨v, hv⟩` from `key Finset.univ`. Conclude with `⟨v, fun i => hv i (Finset.mem_univ i)⟩`.
-/
theorem exists_common_nonzero_of_polynomial_on_lines (V : Type) [AddCommGroup V] [Module ℝ V]
    (ι : Type) [Finite ι] (f : ι → V → ℂ)
    (hpoly : ∀ i a b, ∃ p : Polynomial ℂ, ∀ s : ℝ, f i (a + s • b) = p.eval (s : ℂ))
    (hne : ∀ i, ∃ v, f i v ≠ 0) : ∃ v, ∀ i, f i v ≠ 0 := by
  classical
  have _ := Fintype.ofFinite ι
  have key : ∀ t : Finset ι, ∃ v, ∀ i ∈ t, f i v ≠ 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert j t hj ih =>
      obtain ⟨v, hv⟩ := ih
      obtain ⟨w, hw⟩ := hne j
      choose p hp using fun i => hpoly i v (w - v)
      have hp0 : ∀ i ∈ insert j t, p i ≠ 0 := by
        intro i hi h
        rcases Finset.mem_insert.1 hi with hij | hi
        · subst hij
          apply hw
          have := hp i 1
          simpa [h] using this
        · apply hv i hi
          have := hp i 0
          simpa [h] using this
      have hfin : Set.Finite (⋃ i ∈ (insert j t : Finset ι),
          (fun s : ℝ => (s : ℂ)) ⁻¹' {z | (p i).IsRoot z}) :=
        Set.Finite.biUnion (Finset.finite_toSet _) fun i hi =>
          (Polynomial.finite_setOf_isRoot (hp0 i hi)).preimage Complex.ofReal_injective.injOn
      obtain ⟨s, hs⟩ := hfin.exists_notMem
      refine ⟨v + s • (w - v), fun i hi => ?_⟩
      rw [hp i s]
      intro h0
      apply hs
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq]
      exact ⟨i, hi, h0⟩
  obtain ⟨v, hv⟩ := key Finset.univ
  exact ⟨v, fun i => hv i (Finset.mem_univ i)⟩

end GlobalTheory
