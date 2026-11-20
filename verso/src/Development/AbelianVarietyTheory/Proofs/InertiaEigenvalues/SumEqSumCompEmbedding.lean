import Mathlib

namespace GlobalTheory.EmbeddingSum

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Use symmetry to reverse the relation. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem sum_eq_sum_comp_embedding :
    ∀ {N j : ℕ} (e : Fin j ↪ Fin N) (f : Fin N → ℂ),
      (∀ c ∉ Set.range (⇑e : Fin j → Fin N), f c = (0 : ℂ)) →
      ∑ c : Fin N, f c = ∑ a : Fin j, f ((e : Fin j → Fin N) a) := by
  intro N j e f h
  rw [← Finset.sum_map Finset.univ e f]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro c _ hc
  refine h c ?_
  rintro ⟨a, rfl⟩
  exact hc (Finset.mem_map_of_mem e (Finset.mem_univ a))

end GlobalTheory.EmbeddingSum
