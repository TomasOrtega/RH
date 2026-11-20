import Mathlib

open Polynomial

namespace GlobalTheory

/- English proof (translation)
Use `set v := V.valuation with hv`. Use `set s : Multiset K := Finset.univ.val.map x with hs`. Establish `hcard : Multiset.card s = Fintype.card A` using `by simp [s, Finset.card_univ]`. Establish `hn : 1 ≤ Multiset.card s` using `hcard ▸ Fintype.card_pos_iff.mpr ⟨a⟩`. Establish `hvc : v c ≠ 0` using `(Valuation.ne_zero_iff v).mpr hc`.

Establish `mem_iff : ∀ y : K, y / c ∈ V ↔ v y ≤ v c`. Introduce `y`. Rewrite using `[← V.valuation_le_one_iff, ← hv, map_div₀, div_le_one₀ (zero_lt_iff.mpr hvc)]`. Rewrite using `[mem_iff]`. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Rewrite `hlt` using `[Valuation.map_pow]`. Establish `key : ∀ k, 1 ≤ k → k ≤ Multiset.card s → v (s.esymm k) < v (x a) ^ k`. Introduce `k hk1 hkn`. Take `⟨hkD, hmem⟩` from `h k hk1 (hcard ▸ hkn)`.

Rewrite `hmem` using `[mem_iff, Valuation.map_pow]`. Assume the negation of the conclusion as `hge`. Use `push_neg at hge`. Establish `hp : (v (x a) ^ k) ^ (D / k) ≤ v (s.esymm k) ^ (D / k)` using `pow_le_pow_left₀ zero_le' hge _`. Rewrite `hp` using `[← pow_mul, Nat.mul_div_cancel' hkD]`.

Conclude with `absurd (hp.trans hmem) (not_le.mpr hlt)`. Establish `hpos : 0 < v (x a)`. Use `key 1 le_rfl hn` as an intermediate fact. Rewrite `this` using `[pow_one]`. Conclude with `lt_of_le_of_lt zero_le' this`.

Establish `h0 : (s.map fun t => X - C t).prod.eval (x a) = 0`. Rewrite using `[Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff]`. Simplify using `only [Multiset.map_map, Function.comp_def, eval_sub, eval_X, eval_C]`. Conclude with `Multiset.mem_map.mpr ⟨x a, by simp [s], sub_self _⟩`. Rewrite `h0` using `[Multiset.prod_X_sub_X_eq_sum_esymm, eval_finset_sum, Finset.sum_range_succ']`.

Simplify using `only [eval_mul, eval_pow, eval_neg, eval_one, eval_C, eval_X, pow_zero, one_mul, Nat.sub_zero] at h0`. Establish `he0 : s.esymm 0 = 1` using `by simp [Multiset.esymm, Multiset.powersetCard_zero_left]`. Rewrite `h0` using `[he0, one_mul, ← eq_neg_iff_add_eq_zero]`. Establish `hlt2 : v (∑ j ∈ Finset.range (Multiset.card s), (-1) ^ (j + 1) * (s.esymm (j + 1) * x a ^ (Multiset.card s - (j + 1)))) < v (x a) ^ Multiset.card s`. Apply `Valuation.map_sum_lt _ (pow_ne_zero _ hpos.ne')` to reduce the goal to its premises.

Introduce `j hj`. Establish `hj' : j + 1 ≤ Multiset.card s` using `Finset.mem_range.mp hj`. Rewrite using `[map_mul, map_mul, map_pow, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hlt2` using `[h0, Valuation.map_neg, map_pow]`.

Conclude with `lt_irrefl _ hlt2`.
-/
theorem pow_div_mem_of_esymm_pow_div_mem (K : Type) [Field K] (V : ValuationSubring K)
    (A : Type) [Fintype A] (x : A → K) (D : ℕ) (c : K) (hc : c ≠ 0)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card A →
      k ∣ D ∧ (Finset.univ.val.map x).esymm k ^ (D / k) / c ∈ V) (a : A) :
    x a ^ D / c ∈ V := by
  classical
  set v := V.valuation with hv
  set s : Multiset K := Finset.univ.val.map x with hs
  have hcard : Multiset.card s = Fintype.card A := by simp [s, Finset.card_univ]
  have hn : 1 ≤ Multiset.card s := hcard ▸ Fintype.card_pos_iff.mpr ⟨a⟩
  have hvc : v c ≠ 0 := (Valuation.ne_zero_iff v).mpr hc
  have mem_iff : ∀ y : K, y / c ∈ V ↔ v y ≤ v c := by
    intro y
    rw [← V.valuation_le_one_iff, ← hv, map_div₀, div_le_one₀ (zero_lt_iff.mpr hvc)]
  rw [mem_iff]
  by_contra hlt
  push_neg at hlt
  rw [Valuation.map_pow] at hlt
  have key : ∀ k, 1 ≤ k → k ≤ Multiset.card s → v (s.esymm k) < v (x a) ^ k := by
    intro k hk1 hkn
    obtain ⟨hkD, hmem⟩ := h k hk1 (hcard ▸ hkn)
    rw [mem_iff, Valuation.map_pow] at hmem
    by_contra hge
    push_neg at hge
    have hp : (v (x a) ^ k) ^ (D / k) ≤ v (s.esymm k) ^ (D / k) := pow_le_pow_left₀ zero_le' hge _
    rw [← pow_mul, Nat.mul_div_cancel' hkD] at hp
    exact absurd (hp.trans hmem) (not_le.mpr hlt)
  have hpos : 0 < v (x a) := by
    have := key 1 le_rfl hn
    rw [pow_one] at this
    exact lt_of_le_of_lt zero_le' this
  have h0 : (s.map fun t => X - C t).prod.eval (x a) = 0 := by
    rw [Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff]
    simp only [Multiset.map_map, Function.comp_def, eval_sub, eval_X, eval_C]
    exact Multiset.mem_map.mpr ⟨x a, by simp [s], sub_self _⟩
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, eval_finset_sum, Finset.sum_range_succ'] at h0
  simp only [eval_mul, eval_pow, eval_neg, eval_one, eval_C, eval_X, pow_zero, one_mul,
    Nat.sub_zero] at h0
  have he0 : s.esymm 0 = 1 := by simp [Multiset.esymm, Multiset.powersetCard_zero_left]
  rw [he0, one_mul, ← eq_neg_iff_add_eq_zero] at h0
  have hlt2 : v (∑ j ∈ Finset.range (Multiset.card s),
      (-1) ^ (j + 1) * (s.esymm (j + 1) * x a ^ (Multiset.card s - (j + 1)))) < v (x a) ^ Multiset.card s := by
    apply Valuation.map_sum_lt _ (pow_ne_zero _ hpos.ne')
    intro j hj
    have hj' : j + 1 ≤ Multiset.card s := Finset.mem_range.mp hj
    rw [map_mul, map_mul, map_pow, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    calc v (s.esymm (j + 1)) * v (x a) ^ (Multiset.card s - (j + 1))
        < v (x a) ^ (j + 1) * v (x a) ^ (Multiset.card s - (j + 1)) :=
          mul_lt_mul_of_pos_right (key (j + 1) (Nat.succ_le_succ (Nat.zero_le _)) hj') (pow_pos hpos _)
      _ = v (x a) ^ Multiset.card s := by rw [← pow_add, Nat.add_sub_cancel' hj']
  rw [h0, Valuation.map_neg, map_pow] at hlt2
  exact lt_irrefl _ hlt2

end GlobalTheory
