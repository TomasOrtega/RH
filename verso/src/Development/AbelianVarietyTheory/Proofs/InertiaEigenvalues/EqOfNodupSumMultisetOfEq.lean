import Mathlib

namespace GlobalTheory

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hle : B i + B j ≤ ∑ k, B k`. Rewrite using `[← Finset.sum_pair hne]`. Conclude with `Finset.sum_le_sum_of_subset (Finset.subset_univ _)`. Establish `hnd : (B i + B j).Nodup` using `Multiset.nodup_of_le hle h`.

Rewrite `hnd` using `[← hij]`. Take `⟨a, ha⟩` from `Multiset.exists_mem_of_ne_zero hi`. Conclude with `Multiset.disjoint_left.1 (Multiset.nodup_add.1 hnd).2.2 ha ha`.
-/
theorem eq_of_nodup_sum_multiset_of_eq (ι : Type) [Fintype ι] [DecidableEq ι]
    (B : ι → Multiset ℂ) (h : (∑ i, B i).Nodup) (i j : ι) (hi : B i ≠ 0) (hij : B i = B j) :
    i = j := by
  by_contra hne
  have hle : B i + B j ≤ ∑ k, B k := by
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hnd : (B i + B j).Nodup := Multiset.nodup_of_le hle h
  rw [← hij] at hnd
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hi
  exact Multiset.disjoint_left.1 (Multiset.nodup_add.1 hnd).2.2 ha ha

end GlobalTheory
