import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace

namespace GlobalTheory.AlmostEt

open scoped NNReal

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Use `push_cast`. Conclude with `(v.map_add _ _).trans (max_le ih (by simp))`.
-/
theorem valuation_natCast_le_one {L : Type} [Field L] (v : Valuation L ℝ≥0) (n : ℕ) :
    v (n : L) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (v.map_add _ _).trans (max_le ih (by simp))

/- English proof (translation)
Take `⟨q, rfl⟩ : ∃ q, p = q + 1` from `⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩`. Establish `key : (y + β) ^ (q + 1) - y ^ (q + 1) - β ^ (q + 1) = ∑ i ∈ Finset.range q, y ^ (i + 1) * β ^ (q + 1 - (i + 1)) * ((q + 1).choose (i + 1) : L)`. Rewrite using `[add_pow, Finset.sum_range_succ, Finset.sum_range_succ']`. Simplify using the standard rewrite rules. Rewrite using `[key]`.

Apply `Valuation.map_sum_le` to reduce the goal to its premises. Introduce `i hi`. Establish `hi : i < q` using `Finset.mem_range.mp hi`. Use `set M := max (v y) (v β)`. Take `⟨k, hk⟩` from `hp.dvd_choose_self (Nat.succ_ne_zero i) (by omega)`.

Establish `hsub : q + 1 - (i + 1) = (q - (i + 1)) + 1` using `by omega`. Rewrite using `[hk, hsub]`. Use `push_cast`. Simplify using `only [map_mul, map_pow]`. Establish `h1 : v y ^ (i + 1) ≤ M ^ (i + 1)` using `pow_le_pow_left₀ (by positivity) (le_max_left _ _) _`.

Establish `h2 : v β ^ (q - (i + 1)) ≤ M ^ (q - (i + 1))` using `pow_le_pow_left₀ (by positivity) (le_max_right _ _) _`. Establish `h3 : v (k : L) ≤ 1` using `valuation_natCast_le_one v k`. Establish `hM : M ^ (i + 1) * M ^ (q - (i + 1)) = M ^ q`. Rewrite using `[← pow_add]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[pow_succ (v β)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem valuation_add_pow_sub_le (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ)
    (hp : p.Prime) (y β : L) :
    v ((y + β) ^ p - y ^ p - β ^ p) ≤ v (p : L) * v β * (max (v y) (v β)) ^ (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  have key : (y + β) ^ (q + 1) - y ^ (q + 1) - β ^ (q + 1) =
      ∑ i ∈ Finset.range q, y ^ (i + 1) * β ^ (q + 1 - (i + 1)) * ((q + 1).choose (i + 1) : L) := by
    rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
    simp
  rw [key]
  apply Valuation.map_sum_le
  intro i hi
  have hi : i < q := Finset.mem_range.mp hi
  set M := max (v y) (v β)
  obtain ⟨k, hk⟩ := hp.dvd_choose_self (Nat.succ_ne_zero i) (by omega)
  have hsub : q + 1 - (i + 1) = (q - (i + 1)) + 1 := by omega
  rw [hk, hsub]
  push_cast
  simp only [map_mul, map_pow]
  have h1 : v y ^ (i + 1) ≤ M ^ (i + 1) := pow_le_pow_left₀ (by positivity) (le_max_left _ _) _
  have h2 : v β ^ (q - (i + 1)) ≤ M ^ (q - (i + 1)) := pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
  have h3 : v (k : L) ≤ 1 := valuation_natCast_le_one v k
  have hM : M ^ (i + 1) * M ^ (q - (i + 1)) = M ^ q := by
    rw [← pow_add]; congr 1; omega
  rw [pow_succ (v β)]
  calc _ ≤ M ^ (i + 1) * (M ^ (q - (i + 1)) * v β) * (v ((q : L) + 1) * 1) := by gcongr
    _ = _ := by simp only [Nat.add_sub_cancel, ← hM]; ring

end GlobalTheory.AlmostEt
