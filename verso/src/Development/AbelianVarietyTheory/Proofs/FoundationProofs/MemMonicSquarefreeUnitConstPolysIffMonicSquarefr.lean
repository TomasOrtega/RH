import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

/- English proof (translation)
Unfold `sqSet`. Rewrite using `[Finset.mem_filter, Finset.mem_image, ← and_assoc (a := f.Monic)]`. Use `and_congr_left fun _ => ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨c, -, rfl⟩`. Establish `hd : (∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).degree < N` using `degree_sum_fin_lt c`.

Use `⟨monic_X_pow_add hd, ?_⟩` and prove the remaining obligations. Apply `natDegree_eq_of_degree_eq_some` to reduce the goal to its premises. Rewrite using `[degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]`. Introduce and unpack `⟨hm, rfl⟩`. Use `⟨fun i => f.coeff i, Finset.mem_univ _, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i)]`. Conclude with `hm.as_sum.symm`.
-/
theorem mem_sqSet_iff (g : ℕ) [Fact g.Prime] (N : ℕ) (f : (ZMod g)[X]) :
    f ∈ sqSet g N ↔ f.Monic ∧ f.natDegree = N ∧ Squarefree f ∧ f.coeff 0 ≠ 0 := by
  unfold sqSet
  rw [Finset.mem_filter, Finset.mem_image, ← and_assoc (a := f.Monic)]
  refine and_congr_left fun _ => ⟨?_, ?_⟩
  · rintro ⟨c, -, rfl⟩
    have hd : (∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).degree < N := degree_sum_fin_lt c
    refine ⟨monic_X_pow_add hd, ?_⟩
    apply natDegree_eq_of_degree_eq_some
    rw [degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
  · rintro ⟨hm, rfl⟩
    refine ⟨fun i => f.coeff i, Finset.mem_univ _, ?_⟩
    rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i)]
    exact hm.as_sum.symm

end GlobalTheory.BadShare
