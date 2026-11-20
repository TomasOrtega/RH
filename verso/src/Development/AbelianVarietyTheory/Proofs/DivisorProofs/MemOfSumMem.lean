import Mathlib

namespace GlobalTheory.MembershipOfSum

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on generalizing u with`. Consider the case `empty => intro i hi`. Simplify using `at hi`. Consider the case `insert j S hj ih`. Establish `key : ∀ i ∈ S, u i ∈ F`.

Introduce `i hi`. Establish `hij : i ≠ j` using `fun h => hj (h ▸ hi)`. Take `⟨c, hc⟩` from `hχ i j hij`. Establish `h1 : ∑ l ∈ insert j S, (χ l c - χ j c) • u l ∈ F`. Establish `e : ∑ l ∈ insert j S, (χ l c - χ j c) • u l = ρ c (∑ l ∈ insert j S, u l) - χ j c • ∑ l ∈ insert j S, u l - ∑ l ∈ insert j S, (ρ c (u l) - χ l c • u l)`.

Rewrite using `[map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[sub_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Conclude with `F.sub_mem (F.sub_mem (hF c _ hs) (F.smul_mem _ hs)) (F.sum_mem fun l hl => hu l hl c)`. Rewrite `h1` using `[Finset.sum_insert hj, sub_self, zero_smul, zero_add]`. Establish `h2` using `ih (fun l => (χ l c - χ j c) • u l) (by`. Introduce `l hl d`. Use `F.smul_mem (χ l c - χ j c) (hu l (Finset.mem_insert_of_mem hl) d)` as an intermediate fact.

Rewrite `this` using `[smul_sub, smul_comm]`. Rewrite using `[map_smul]`. Conclude with `this) h1 i hi`. Conclude with `(F.smul_mem_iff (sub_ne_zero.mpr hc)).mp h2`. Introduce `i hi`.

Break down `Finset.mem_insert.mp hi with rfl | hi` into its components or cases. Rewrite `hs` using `[Finset.sum_insert hj]`. Use `F.sub_mem hs (F.sum_mem key)` as an intermediate fact. Simplify using `using this`. Conclude with `key i hi`.
-/
theorem mem_of_sum_mem {k : Type} [Field k] {H : Type 1} [AddCommGroup H] [Module k H]
    {O : Type} [CommRing O] (ρ : O →+* Module.End k H) (F : Submodule k H)
    (hF : ∀ (c : O), ∀ x ∈ F, ρ c x ∈ F) {a : ℕ} (χ : Fin a → O → k)
    (hχ : ∀ (i j : Fin a), i ≠ j → ∃ (c : O), χ i c ≠ χ j c) (S : Finset (Fin a))
    (u : Fin a → H) (hu : ∀ i ∈ S, ∀ (c : O), ρ c (u i) - χ i c • u i ∈ F)
    (hs : ∑ i ∈ S, u i ∈ F) : ∀ i ∈ S, u i ∈ F := by
  induction S using Finset.induction_on generalizing u with
  | empty => intro i hi; simp at hi
  | insert j S hj ih =>
    have key : ∀ i ∈ S, u i ∈ F := by
      intro i hi
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      obtain ⟨c, hc⟩ := hχ i j hij
      have h1 : ∑ l ∈ insert j S, (χ l c - χ j c) • u l ∈ F := by
        have e : ∑ l ∈ insert j S, (χ l c - χ j c) • u l =
            ρ c (∑ l ∈ insert j S, u l) - χ j c • ∑ l ∈ insert j S, u l
              - ∑ l ∈ insert j S, (ρ c (u l) - χ l c • u l) := by
          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [sub_smul]; abel
        rw [e]
        exact F.sub_mem (F.sub_mem (hF c _ hs) (F.smul_mem _ hs))
          (F.sum_mem fun l hl => hu l hl c)
      rw [Finset.sum_insert hj, sub_self, zero_smul, zero_add] at h1
      have h2 := ih (fun l => (χ l c - χ j c) • u l) (by
        intro l hl d
        have := F.smul_mem (χ l c - χ j c) (hu l (Finset.mem_insert_of_mem hl) d)
        rw [smul_sub, smul_comm] at this
        rw [map_smul]
        exact this) h1 i hi
      exact (F.smul_mem_iff (sub_ne_zero.mpr hc)).mp h2
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [Finset.sum_insert hj] at hs
      have := F.sub_mem hs (F.sum_mem key)
      simpa using this
    · exact key i hi

end GlobalTheory.MembershipOfSum
