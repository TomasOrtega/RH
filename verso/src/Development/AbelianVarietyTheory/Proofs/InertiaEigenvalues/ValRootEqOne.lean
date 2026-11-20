import Mathlib

namespace GlobalTheory.RootValuationOne

open Finset

/- English proof (translation)
Rewrite using `[← geom_sum₂_mul, map_mul]`. Establish `hs : A.valuation (∑ j ∈ range i, x ^ j * y ^ (i - 1 - j)) ≤ 1`. Apply `Valuation.map_sum_le` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[map_mul, map_pow, map_pow]`.

Conclude with `mul_le_one' (pow_le_one' hx _) (pow_le_one' hy _)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sub_pow_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {x y : Ω}
    (hx : A.valuation x ≤ 1) (hy : A.valuation y ≤ 1) (hd : A.valuation (x - y) < 1) (i : ℕ) :
    A.valuation (x ^ i - y ^ i) < 1 := by
  rw [← geom_sum₂_mul, map_mul]
  have hs : A.valuation (∑ j ∈ range i, x ^ j * y ^ (i - 1 - j)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro j _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one' (pow_le_one' hx _) (pow_le_one' hy _)
  calc _ ≤ 1 * A.valuation (x - y) := by gcongr
    _ < 1 := by rw [one_mul]; exact hd

/- English proof (translation)
Establish `h : A.valuation x ^ n = 1` using `by rw [← map_pow, hx, map_one]`. Break down `lt_trichotomy (A.valuation x) 1 with h' | h' | h'` into its components or cases. Conclude with `absurd h (pow_lt_one₀ zero_le' h' hn0).ne`. Conclude with `h'`. Conclude with `absurd h (one_lt_pow₀ h' hn0).ne'`.
-/
theorem val_root_eq_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {n : ℕ} (hn0 : n ≠ 0)
    {x : Ω} (hx : x ^ n = 1) : A.valuation x = 1 := by
  have h : A.valuation x ^ n = 1 := by rw [← map_pow, hx, map_one]
  rcases lt_trichotomy (A.valuation x) 1 with h' | h' | h'
  · exact absurd h (pow_lt_one₀ zero_le' h' hn0).ne
  · exact h'
  · exact absurd h (one_lt_pow₀ h' hn0).ne'

/- English proof (translation)
Introduce `Ω _ A n hn ξ ξ' h1 h2 hd`. Establish `hn0 : n ≠ 0` using `by rintro rfl; apply hn; simp`. Establish `hv1` using `val_root_eq_one A hn0 h1`. Establish `hv2` using `val_root_eq_one A hn0 h2`. Assume the negation of the conclusion as `hne`.

Establish `hs : ∑ i ∈ range n, ξ ^ i * ξ' ^ (n - 1 - i) = 0`. Use `geom_sum₂_mul ξ ξ' n` as an intermediate fact. Rewrite `this` using `[h1, h2, sub_self]`. Conclude with `(mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)`. Establish `hlt : A.valuation (∑ i ∈ range n, (ξ ^ i * ξ' ^ (n - 1 - i) - ξ' ^ (n - 1))) < 1`.

Apply `Valuation.map_sum_lt _ one_ne_zero` to reduce the goal to its premises. Introduce `i hi`. Establish `hi' : i + (n - 1 - i) = n - 1`. Use `mem_range.mp hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `e : ξ ^ i * ξ' ^ (n - 1 - i) - ξ' ^ (n - 1) = (ξ ^ i - ξ' ^ i) * ξ' ^ (n - 1 - i)`. Rewrite using `[sub_mul, ← pow_add, hi']`. Rewrite using `[e, map_mul, map_pow, hv2, one_pow, mul_one]`. Conclude with `sub_pow_lt_one A hv1.le hv2.le hd i`. Rewrite `hlt` using `[sum_sub_distrib, hs, sum_const, card_range, zero_sub, Valuation.map_neg, nsmul_eq_mul, map_mul, map_pow, hv2, one_pow, mul_one]`.

Conclude with `hn hlt`.
-/
theorem main : ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω) (n : ℕ),
    ¬(ValuationSubring.valuation A : Ω → ValuationSubring.ValueGroup A) (↑n : Ω) < (1 : ValuationSubring.ValueGroup A) →
    ∀ {ξ ξ' : Ω}, ξ ^ n = (1 : Ω) → ξ' ^ n = (1 : Ω) →
    (ValuationSubring.valuation A : Ω → ValuationSubring.ValueGroup A) (ξ - ξ') < (1 : ValuationSubring.ValueGroup A) → ξ = ξ' := by
  intro Ω _ A n hn ξ ξ' h1 h2 hd
  have hn0 : n ≠ 0 := by rintro rfl; apply hn; simp
  have hv1 := val_root_eq_one A hn0 h1
  have hv2 := val_root_eq_one A hn0 h2
  by_contra hne
  have hs : ∑ i ∈ range n, ξ ^ i * ξ' ^ (n - 1 - i) = 0 := by
    have := geom_sum₂_mul ξ ξ' n
    rw [h1, h2, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have hlt : A.valuation (∑ i ∈ range n, (ξ ^ i * ξ' ^ (n - 1 - i) - ξ' ^ (n - 1))) < 1 := by
    apply Valuation.map_sum_lt _ one_ne_zero
    intro i hi
    have hi' : i + (n - 1 - i) = n - 1 := by
      have := mem_range.mp hi; omega
    have e : ξ ^ i * ξ' ^ (n - 1 - i) - ξ' ^ (n - 1) = (ξ ^ i - ξ' ^ i) * ξ' ^ (n - 1 - i) := by
      rw [sub_mul, ← pow_add, hi']
    rw [e, map_mul, map_pow, hv2, one_pow, mul_one]
    exact sub_pow_lt_one A hv1.le hv2.le hd i
  rw [sum_sub_distrib, hs, sum_const, card_range, zero_sub, Valuation.map_neg, nsmul_eq_mul,
    map_mul, map_pow, hv2, one_pow, mul_one] at hlt
  exact hn hlt

end GlobalTheory.RootValuationOne
