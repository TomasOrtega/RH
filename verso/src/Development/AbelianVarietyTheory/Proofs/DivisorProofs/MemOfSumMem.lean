import Mathlib

namespace GlobalTheory.MembershipOfSum

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
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
