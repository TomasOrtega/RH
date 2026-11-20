import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Finset

def monicDifferenceCoeff {d : ℕ} (C : Fin d → ℂ) (s : ℂ) (j : Fin d) : ℂ :=
  s ^ (d - 1 - (j : ℕ)) + ∑ k ∈ univ.filter (fun k : Fin d => (j : ℕ) < k), C k * s ^ ((k : ℕ) - 1 - j)

/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range (fun j => if j < m then f j else 0) n, ← Finset.sum_filter]`. Use `congr 1`. Use extensionality with `j`. Simplify using `only [mem_filter, mem_range]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_fin_ite_lt {n m : ℕ} (hm : m ≤ n) (f : ℕ → ℂ) :
    ∑ j : Fin n, (if (j : ℕ) < m then f j else 0) = ∑ j ∈ range m, f j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < m then f j else 0) n, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [mem_filter, mem_range]
  omega

/- English proof (translation)
Rewrite using `[sum_fin_ite_lt hm (fun j => s ^ (m - 1 - j) * t ^ j), mul_comm]`. Establish `h` using `geom_sum₂_mul s t m`. Rewrite `h` using `[geom_sum₂_comm]`. Rewrite using `[← h]`. Use `congr 1`.

Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`.
-/
theorem sub_pow_eq_mul_sum_fin {n m : ℕ} (hm : m ≤ n) (s t : ℂ) :
    (s - t) * ∑ j : Fin n, (if (j : ℕ) < m then s ^ (m - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0) = s ^ m - t ^ m := by
  rw [sum_fin_ite_lt hm (fun j => s ^ (m - 1 - j) * t ^ j), mul_comm]
  have h := geom_sum₂_mul s t m
  rw [geom_sum₂_comm] at h
  rw [← h]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/- English proof (translation)
Establish `expand : ∑ j : Fin d, monicDifferenceCoeff C s j * t ^ (j : ℕ) = ∑ j : Fin d, (if (j : ℕ) < d then s ^ (d - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0) + ∑ k : Fin d, C k * ∑ j : Fin d, (if (j : ℕ) < k then s ^ ((k : ℕ) - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0)`. Simplify using `only [monicDifferenceCoeff, add_mul, Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_mul]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j _ => by simp [j.isLt]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> ring`. Establish `h2 : ∑ k : Fin d, (s - t) * (C k * ∑ j : Fin d, (if (j : ℕ) < k then s ^ ((k : ℕ) - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0)) = ∑ k : Fin d, (C k * s ^ (k : ℕ) - C k * t ^ (k : ℕ))` using `Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, sub_pow_eq_mul_sum_fin k.isLt.le, mul_sub]`.

Rewrite using `[expand, mul_add, sub_pow_eq_mul_sum_fin le_rfl, Finset.mul_sum, h2, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem monic_sub_eq_mul_sum {d : ℕ} (C : Fin d → ℂ) (s t : ℂ) :
    (s ^ d + ∑ k : Fin d, C k * s ^ (k : ℕ)) - (t ^ d + ∑ k : Fin d, C k * t ^ (k : ℕ)) =
      (s - t) * ∑ j : Fin d, monicDifferenceCoeff C s j * t ^ (j : ℕ) := by
  have expand : ∑ j : Fin d, monicDifferenceCoeff C s j * t ^ (j : ℕ) =
      ∑ j : Fin d, (if (j : ℕ) < d then s ^ (d - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0) +
        ∑ k : Fin d, C k * ∑ j : Fin d,
          (if (j : ℕ) < k then s ^ ((k : ℕ) - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0) := by
    simp only [monicDifferenceCoeff, add_mul, Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by simp [j.isLt]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
  have h2 : ∑ k : Fin d, (s - t) * (C k * ∑ j : Fin d,
      (if (j : ℕ) < k then s ^ ((k : ℕ) - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0)) =
      ∑ k : Fin d, (C k * s ^ (k : ℕ) - C k * t ^ (k : ℕ)) :=
    Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, sub_pow_eq_mul_sum_fin k.isLt.le, mul_sub]
  rw [expand, mul_add, sub_pow_eq_mul_sum_fin le_rfl, Finset.mul_sum, h2, Finset.sum_sub_distrib]
  ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
