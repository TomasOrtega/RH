import Mathlib

namespace GlobalTheory.EmbeddingSum

/- English proof (translation)
Introduce `N j e f h`. Rewrite using `[← Finset.sum_map Finset.univ e f]`. Use `symm`. Use `Finset.sum_subset (Finset.subset_univ _) ?_` and prove the remaining obligations. Introduce `c _ hc`.

Use `h c ?_` and prove the remaining obligations. Introduce and unpack `⟨a, rfl⟩`. Conclude with `hc (Finset.mem_map_of_mem e (Finset.mem_univ a))`.
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
