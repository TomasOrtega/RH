import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory

/- English proof (translation)
Establish `hpow : ∀ j : ℕ, ω ^ (j * n) = (ω ^ n) ^ j` using `fun j => by rw [← pow_mul, mul_comm]`. Repeatedly rewrite using `[hpow]`. Use `split_ifs with hn`. Rewrite using `[(hω.pow_eq_one_iff_dvd n).mpr hn]`. Simplify using the standard rewrite rules.

Establish `hne : ω ^ n ≠ 1` using `fun h => hn ((hω.pow_eq_one_iff_dvd n).mp h)`. Establish `h63 : (ω ^ n) ^ 63 = 1`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]`. Establish `hg` using `geom_sum_mul (ω ^ n) 63`. Rewrite `hg` using `[h63, sub_self]`.

Conclude with `(mul_eq_zero.mp hg).resolve_right (sub_ne_zero.mpr hne)`.
-/
private theorem sum_range_63_primitiveRoot_pow_eq_ite (ω : ℂ) (hω : IsPrimitiveRoot ω 63) (n : ℕ) :
    ∑ j ∈ Finset.range 63, ω ^ (j * n) = if 63 ∣ n then (63 : ℂ) else 0 := by
  have hpow : ∀ j : ℕ, ω ^ (j * n) = (ω ^ n) ^ j := fun j => by rw [← pow_mul, mul_comm]
  simp_rw [hpow]
  split_ifs with hn
  · rw [(hω.pow_eq_one_iff_dvd n).mpr hn]
    simp
  · have hne : ω ^ n ≠ 1 := fun h => hn ((hω.pow_eq_one_iff_dvd n).mp h)
    have h63 : (ω ^ n) ^ 63 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    have hg := geom_sum_mul (ω ^ n) 63
    rw [h63, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_right (sub_ne_zero.mpr hne)

/- English proof (translation)
Establish `hsum` using `sum_range_63_primitiveRoot_pow_eq_ite ω hω`. Combine the equalities or inequalities in the displayed calculation. Repeatedly rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_add, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑ k ∈ Finset.range 63, (c k : ℂ) * (if 63 ∣ k + 62 * m then (63 : ℂ) else 0) := by`. Repeatedly rewrite using `[hsum]`. Use `_ = 63 * (c m : ℂ) := by`.

Rewrite using `[Finset.sum_eq_single m]`. Rewrite using `[if_pos (by omega)]`. Expand and normalize the polynomial expressions, which then agree. Introduce `k hk hkm`. Establish `hk'` using `Finset.mem_range.mp hk`.

Rewrite using `[if_neg (by omega)]`. Simplify using the standard rewrite rules. Introduce `hm'`. Conclude with `absurd (Finset.mem_range.mpr hm) hm'`.
-/
theorem fourier_inv_sixtythree (ω : ℂ) (c : ℕ → ℤ) (hω : IsPrimitiveRoot ω 63) (m : ℕ)
    (hm : m < 63) :
    ∑ j ∈ Finset.range 63, (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * m))
      = 63 * (c m : ℂ) := by
  have hsum := sum_range_63_primitiveRoot_pow_eq_ite ω hω
  calc ∑ j ∈ Finset.range 63, (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * m))
      = ∑ k ∈ Finset.range 63, (c k : ℂ) * ∑ j ∈ Finset.range 63, ω ^ (j * (k + 62 * m)) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_add, pow_add]
        ring
    _ = ∑ k ∈ Finset.range 63, (c k : ℂ) * (if 63 ∣ k + 62 * m then (63 : ℂ) else 0) := by
        simp_rw [hsum]
    _ = 63 * (c m : ℂ) := by
        rw [Finset.sum_eq_single m]
        · rw [if_pos (by omega)]
          ring
        · intro k hk hkm
          have hk' := Finset.mem_range.mp hk
          rw [if_neg (by omega)]
          simp
        · intro hm'
          exact absurd (Finset.mem_range.mpr hm) hm'

/- English proof (translation)
Establish `key : ∀ n, n < 63 → (63 : ℂ) * (c n : ℂ) = ∑ j ∈ Finset.range 63, (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * n))` using `fun n hn => (fourier_inv_sixtythree ω c hω n hn).symm`. Establish `hz : ∑ j ∈ Finset.range 63, ((∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * (m + 10))) - (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * (m + 3))) - (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * (m + 7))) + (∑ k ∈ Finset.ra …`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j hj`. Establish `hj'` using `Finset.mem_range.mp hj`.

Distinguish the cases in `h21 : 21 ∣ j`. Establish `hB : ω ^ (186 * j) = 1` using `(hω.pow_eq_one_iff_dvd _).mpr (by omega)`. Rewrite using `[show j * (62 * (m + 10)) = j * (62 * (m + 7)) + 186 * j by ring, show j * (62 * (m + 3)) = j * (62 * m) + 186 * j by ring, pow_add, pow_add, hB]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `h9 : 9 ∣ j`.

Establish `hB : ω ^ (434 * j) = 1` using `(hω.pow_eq_one_iff_dvd _).mpr (by omega)`. Rewrite using `[show j * (62 * (m + 10)) = j * (62 * (m + 3)) + 434 * j by ring, show j * (62 * (m + 7)) = j * (62 * m) + 434 * j by ring, pow_add, pow_add, hB]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h j hj' h21 h9]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h63 : (63 : ℂ) * ((c (m + 10) : ℂ) - c (m + 3) - c (m + 7) + c m) = 0`. Rewrite using `[mul_add, mul_sub, mul_sub, key (m + 10) (by omega), key (m + 3) (by omega), key (m + 7) (by omega), key m (by omega), ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`. Conclude with `hz`. Establish `h' : (c (m + 10) : ℂ) - c (m + 3) - c (m + 7) + c m = 0` using `(mul_eq_zero.mp h63).resolve_left (by norm_num)`. Establish `h'' : ((c (m + 10) - c (m + 3) - c (m + 7) + c m : ℤ) : ℂ) = 0`.

Use `push_cast`. Conclude with `h'`. Establish `h3` using `Int.cast_eq_zero.mp h''`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mixed_diff_sixtythree (ω : ℂ) (c : ℕ → ℤ) (hω : IsPrimitiveRoot ω 63)
    (h : ∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j →
      ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) (m : ℕ) (hm : m < 53) :
    c (m + 10) - c (m + 3) = c (m + 7) - c m := by
  have key : ∀ n, n < 63 → (63 : ℂ) * (c n : ℂ) = ∑ j ∈ Finset.range 63,
      (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * n)) :=
    fun n hn => (fourier_inv_sixtythree ω c hω n hn).symm
  have hz : ∑ j ∈ Finset.range 63,
      ((∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * (m + 10)))
        - (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * (m + 3)))
        - (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * (m + 7)))
        + (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * m))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_range.mp hj
    by_cases h21 : 21 ∣ j
    · have hB : ω ^ (186 * j) = 1 := (hω.pow_eq_one_iff_dvd _).mpr (by omega)
      rw [show j * (62 * (m + 10)) = j * (62 * (m + 7)) + 186 * j by ring,
        show j * (62 * (m + 3)) = j * (62 * m) + 186 * j by ring, pow_add, pow_add, hB]
      ring
    · by_cases h9 : 9 ∣ j
      · have hB : ω ^ (434 * j) = 1 := (hω.pow_eq_one_iff_dvd _).mpr (by omega)
        rw [show j * (62 * (m + 10)) = j * (62 * (m + 3)) + 434 * j by ring,
          show j * (62 * (m + 7)) = j * (62 * m) + 434 * j by ring, pow_add, pow_add, hB]
        ring
      · rw [h j hj' h21 h9]
        ring
  have h63 : (63 : ℂ) * ((c (m + 10) : ℂ) - c (m + 3) - c (m + 7) + c m) = 0 := by
    rw [mul_add, mul_sub, mul_sub, key (m + 10) (by omega), key (m + 3) (by omega),
      key (m + 7) (by omega), key m (by omega), ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact hz
  have h' : (c (m + 10) : ℂ) - c (m + 3) - c (m + 7) + c m = 0 :=
    (mul_eq_zero.mp h63).resolve_left (by norm_num)
  have h'' : ((c (m + 10) - c (m + 3) - c (m + 7) + c m : ℤ) : ℂ) = 0 := by
    push_cast
    exact h'
  have h3 := Int.cast_eq_zero.mp h''
  linarith

/- English proof (translation)
Establish `hs : ∑ j ∈ Finset.range 63, (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * (n + 21))) = ∑ j ∈ Finset.range 63, (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * n))`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hj'` using `Finset.mem_range.mp hj`. Distinguish the cases in `h3 : 3 ∣ j`. Establish `hB : ω ^ (1302 * j) = 1` using `(hω.pow_eq_one_iff_dvd _).mpr (by omega)`.

Rewrite using `[show j * (62 * (n + 21)) = j * (62 * n) + 1302 * j by ring, pow_add, hB, mul_one]`. Rewrite using `[h j hj' (by omega) (by omega), zero_mul, zero_mul]`. Establish `e1` using `fourier_inv_sixtythree ω c hω (n + 21) (by omega)`. Rewrite `e1` using `[hs, fourier_inv_sixtythree ω c hω n (by omega)]`. Establish `e2 : ((c (n + 21) : ℤ) : ℂ) = (c n : ℂ)` using `(mul_left_cancel₀ (by norm_num : (63 : ℂ) ≠ 0) e1).symm`.

Conclude with `e2` after adjusting the coercions.
-/
private theorem apply_add_21_eq_of_fourier_vanish_order_63 (ω : ℂ) (c : ℕ → ℤ) (hω : IsPrimitiveRoot ω 63)
    (h : ∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j →
      ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) (n : ℕ) (hn : n < 42) :
    c (n + 21) = c n := by
  have hs : ∑ j ∈ Finset.range 63,
      (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * (n + 21)))
      = ∑ j ∈ Finset.range 63,
      (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * n)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    by_cases h3 : 3 ∣ j
    · have hB : ω ^ (1302 * j) = 1 := (hω.pow_eq_one_iff_dvd _).mpr (by omega)
      rw [show j * (62 * (n + 21)) = j * (62 * n) + 1302 * j by ring, pow_add, hB, mul_one]
    · rw [h j hj' (by omega) (by omega), zero_mul, zero_mul]
  have e1 := fourier_inv_sixtythree ω c hω (n + 21) (by omega)
  rw [hs, fourier_inv_sixtythree ω c hω n (by omega)] at e1
  have e2 : ((c (n + 21) : ℤ) : ℂ) = (c n : ℂ) :=
    (mul_left_cancel₀ (by norm_num : (63 : ℂ) ≠ 0) e1).symm
  exact_mod_cast e2

/- English proof (translation)
Introduce `ω c hω hnorm hF`. Establish `hrel` using `fun m (hm : m < 53) => mixed_diff_sixtythree ω c hω hF m hm`. Establish `hper` using `fun n (hn : n < 42) => apply_add_21_eq_of_fourier_vanish_order_63 ω c hω hF n hn`. Establish `hD : ∀ m, m < 56 → c (m + 7) - c m = c (m % 3 + 7) - c (m % 3)`. Introduce `m`.

Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`. Introduce `hm`. Distinguish the cases in `h3 : m < 3`. Rewrite using `[Nat.mod_eq_of_lt h3]`.

Take `⟨m', rfl⟩ : ∃ m', m = m' + 3` from `⟨m - 3, by omega⟩`. Establish `e1` using `hrel m' (by omega)`. Establish `e2` using `ih m' (by omega) (by omega)`. Rewrite using `[show (m' + 3) % 3 = m' % 3 by omega, show m' + 3 + 7 = m' + 10 by omega]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hS : ∑ k ∈ Finset.range 63, c k ^ 2 = 3 * ∑ k ∈ Finset.range 21, c k ^ 2`. Rewrite using `[show (63 : ℕ) = 21 + 21 + 21 from rfl, Finset.sum_range_add, Finset.sum_range_add]`. Establish `h1 : ∑ x ∈ Finset.range 21, c (21 + x) ^ 2 = ∑ x ∈ Finset.range 21, c x ^ 2` using `Finset.sum_congr rfl fun x hx => by`. Rewrite using `[add_comm, hper x (by have := Finset.mem_range.mp hx; omega)]`. Establish `h2 : ∑ x ∈ Finset.range 21, c (21 + 21 + x) ^ 2 = ∑ x ∈ Finset.range 21, c x ^ 2` using `Finset.sum_congr rfl fun x hx => by`.

Establish `hx'` using `Finset.mem_range.mp hx`. Rewrite using `[show 21 + 21 + x = x + 21 + 21 by omega, hper (x + 21) (by omega), hper x (by omega)]`. Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcolsum : ∑ k ∈ Finset.range 21, c k ^ 2 = ∑ b ∈ Finset.range 7, (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2)`.

Rewrite using `[show (21 : ℕ) = 7 + 7 + 7 from rfl, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_add_distrib, Finset.sum_add_distrib]`. Establish `h1 : ∑ x ∈ Finset.range 7, c (7 + x) ^ 2 = ∑ x ∈ Finset.range 7, c (x + 7) ^ 2` using `Finset.sum_congr rfl fun x _ => by rw [add_comm]`. Establish `h2 : ∑ x ∈ Finset.range 7, c (7 + 7 + x) ^ 2 = ∑ x ∈ Finset.range 7, c (x + 14) ^ 2` using `Finset.sum_congr rfl fun x _ => by rw [show 7 + 7 + x = x + 14 by omega]`. Rewrite using `[h1, h2]`. Establish `hcol : ∀ b, b < 7 → (c 7 - c 0) ^ 2 + (c 8 - c 1) ^ 2 + (c 9 - c 2) ^ 2 ≤ 3 * (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2)`.

Introduce `b hb`. Establish `e1` using `hD b (by omega)`. Establish `e2` using `hD (b + 7) (by omega)`. Establish `e3` using `hD (b + 14) (by omega)`. Establish `p` using `hper b (by omega)`.

Rewrite `e2` using `[show b + 7 + 7 = b + 14 by omega]`. Rewrite `e3` using `[show b + 14 + 7 = b + 21 by omega, p]`. Establish `key : (c (b + 7) - c b) ^ 2 + (c (b + 14) - c (b + 7)) ^ 2 + (c b - c (b + 14)) ^ 2 ≤ 3 * (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2)`. Use polynomial arithmetic with `[sq_nonneg (c b + c (b + 7) + c (b + 14))]`. Rewrite `key` using `[e1, e2, e3]`.

Establish `hb3 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2` using `by omega`. Break down `hb3 with h | h | h` into its components or cases. Rewrite `key` using `[show (b + 7) % 3 = 1 by omega, show (b + 14) % 3 = 2 by omega, h]`. Evaluate the numerical expressions using `at key`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite `key` using `[show (b + 7) % 3 = 2 by omega, show (b + 14) % 3 = 0 by omega, h]`. Evaluate the numerical expressions using `at key`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `key` using `[show (b + 7) % 3 = 0 by omega, show (b + 14) % 3 = 1 by omega, h]`. Evaluate the numerical expressions using `at key`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hnorm` using `[hS]`. Establish `hS21 : ∑ k ∈ Finset.range 21, c k ^ 2 = 4` using `by omega`. Establish `hΔ : 7 * ((c 7 - c 0) ^ 2 + (c 8 - c 1) ^ 2 + (c 9 - c 2) ^ 2) ≤ 12`. Establish `hle` using `Finset.sum_le_sum (s := Finset.range 7) fun b hb => hcol b (Finset.mem_range.mp hb)`.

Rewrite `hle` using `[← Finset.mul_sum, ← hcolsum, hS21]`. Simplify using `only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle`. Move the coercions through the operations in `at hle`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum0 : (c 7 - c 0) + (c 8 - c 1) + (c 9 - c 2) = 0`.

Establish `e2` using `hD 7 (by omega)`. Establish `e3` using `hD 14 (by omega)`. Establish `p` using `hper 0 (by omega)`. Evaluate the numerical expressions using `at e2 e3 p`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hzero : c 7 - c 0 = 0 ∧ c 8 - c 1 = 0 ∧ c 9 - c 2 = 0`. Generalize the expression as in `c 7 - c 0 = x at hΔ hsum0 ⊢`. Generalize the expression as in `c 8 - c 1 = y at hΔ hsum0 ⊢`. Generalize the expression as in `c 9 - c 2 = z at hΔ hsum0 ⊢`. Establish `hz : z = -x - y` using `by linarith`.

Substitute `hz` using the available equality. Establish `h14 : 14 * (x ^ 2 + x * y + y ^ 2) ≤ 12` using `by nlinarith`. Establish `hq : x ^ 2 + x * y + y ^ 2 ≤ 0` using `by omega`. Establish `hy2 : y ^ 2 ≤ 0` using `by nlinarith [sq_nonneg (2 * x + y)]`. Establish `hy : y = 0` using `(pow_eq_zero_iff two_ne_zero).mp (le_antisymm hy2 (sq_nonneg y))`.

Substitute `hy` using the available equality. Establish `hx2 : x ^ 2 ≤ 0` using `by nlinarith`. Establish `hx : x = 0` using `(pow_eq_zero_iff two_ne_zero).mp (le_antisymm hx2 (sq_nonneg x))`. Substitute `hx` using the available equality. Evaluate the numerical expressions.

Establish `hp7 : ∀ r, r < 3 → c (r + 7) = c r`. Introduce `r hr`. Apply the tactic sequence `interval_cases r <;> norm_num <;> omega`. Establish `hcolc : ∀ b, b < 7 → c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2 = 3 * c b ^ 2`. Introduce `b hb`.

Establish `e1` using `hD b (by omega)`. Establish `e2` using `hD (b + 7) (by omega)`. Rewrite `e2` using `[show b + 7 + 7 = b + 14 by omega]`. Rewrite `e1` using `[hp7 (b % 3) (Nat.mod_lt _ (by norm_num))]`. Rewrite `e2` using `[hp7 ((b + 7) % 3) (Nat.mod_lt _ (by norm_num))]`.

Establish `h1 : c (b + 7) = c b` using `by linarith`. Establish `h2 : c (b + 14) = c b` using `by linarith`. Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ∑ b ∈ Finset.range 7, (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2) = 3 * ∑ b ∈ Finset.range 7, c b ^ 2`.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun b hb => hcolc b (Finset.mem_range.mp hb)`. Rewrite `hS21` using `[hcolsum, h3]`. Use linear arithmetic over natural numbers and integers.
-/
theorem no_norm_twelve_order_sixtythree : ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 63 →
    ∑ k ∈ Finset.range 63, c k ^ 2 = 12 →
    (∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j →
      ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  intro ω c hω hnorm hF
  have hrel := fun m (hm : m < 53) => mixed_diff_sixtythree ω c hω hF m hm
  have hper := fun n (hn : n < 42) => apply_add_21_eq_of_fourier_vanish_order_63 ω c hω hF n hn
  have hD : ∀ m, m < 56 → c (m + 7) - c m = c (m % 3 + 7) - c (m % 3) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      by_cases h3 : m < 3
      · rw [Nat.mod_eq_of_lt h3]
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
        have e1 := hrel m' (by omega)
        have e2 := ih m' (by omega) (by omega)
        rw [show (m' + 3) % 3 = m' % 3 by omega, show m' + 3 + 7 = m' + 10 by omega]
        linarith
  have hS : ∑ k ∈ Finset.range 63, c k ^ 2 = 3 * ∑ k ∈ Finset.range 21, c k ^ 2 := by
    rw [show (63 : ℕ) = 21 + 21 + 21 from rfl, Finset.sum_range_add, Finset.sum_range_add]
    have h1 : ∑ x ∈ Finset.range 21, c (21 + x) ^ 2 = ∑ x ∈ Finset.range 21, c x ^ 2 :=
      Finset.sum_congr rfl fun x hx => by
        rw [add_comm, hper x (by have := Finset.mem_range.mp hx; omega)]
    have h2 : ∑ x ∈ Finset.range 21, c (21 + 21 + x) ^ 2 = ∑ x ∈ Finset.range 21, c x ^ 2 :=
      Finset.sum_congr rfl fun x hx => by
        have hx' := Finset.mem_range.mp hx
        rw [show 21 + 21 + x = x + 21 + 21 by omega, hper (x + 21) (by omega), hper x (by omega)]
    rw [h1, h2]
    ring
  have hcolsum : ∑ k ∈ Finset.range 21, c k ^ 2 =
      ∑ b ∈ Finset.range 7, (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2) := by
    rw [show (21 : ℕ) = 7 + 7 + 7 from rfl, Finset.sum_range_add, Finset.sum_range_add,
      Finset.sum_add_distrib, Finset.sum_add_distrib]
    have h1 : ∑ x ∈ Finset.range 7, c (7 + x) ^ 2 = ∑ x ∈ Finset.range 7, c (x + 7) ^ 2 :=
      Finset.sum_congr rfl fun x _ => by rw [add_comm]
    have h2 : ∑ x ∈ Finset.range 7, c (7 + 7 + x) ^ 2 = ∑ x ∈ Finset.range 7, c (x + 14) ^ 2 :=
      Finset.sum_congr rfl fun x _ => by rw [show 7 + 7 + x = x + 14 by omega]
    rw [h1, h2]
  have hcol : ∀ b, b < 7 → (c 7 - c 0) ^ 2 + (c 8 - c 1) ^ 2 + (c 9 - c 2) ^ 2 ≤
      3 * (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2) := by
    intro b hb
    have e1 := hD b (by omega)
    have e2 := hD (b + 7) (by omega)
    have e3 := hD (b + 14) (by omega)
    have p := hper b (by omega)
    rw [show b + 7 + 7 = b + 14 by omega] at e2
    rw [show b + 14 + 7 = b + 21 by omega, p] at e3
    have key : (c (b + 7) - c b) ^ 2 + (c (b + 14) - c (b + 7)) ^ 2 + (c b - c (b + 14)) ^ 2 ≤
        3 * (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2) := by
      nlinarith [sq_nonneg (c b + c (b + 7) + c (b + 14))]
    rw [e1, e2, e3] at key
    have hb3 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases hb3 with h | h | h
    · rw [show (b + 7) % 3 = 1 by omega, show (b + 14) % 3 = 2 by omega, h] at key
      norm_num at key
      linarith
    · rw [show (b + 7) % 3 = 2 by omega, show (b + 14) % 3 = 0 by omega, h] at key
      norm_num at key
      linarith
    · rw [show (b + 7) % 3 = 0 by omega, show (b + 14) % 3 = 1 by omega, h] at key
      norm_num at key
      linarith
  rw [hS] at hnorm
  have hS21 : ∑ k ∈ Finset.range 21, c k ^ 2 = 4 := by omega
  have hΔ : 7 * ((c 7 - c 0) ^ 2 + (c 8 - c 1) ^ 2 + (c 9 - c 2) ^ 2) ≤ 12 := by
    have hle := Finset.sum_le_sum (s := Finset.range 7) fun b hb => hcol b (Finset.mem_range.mp hb)
    rw [← Finset.mul_sum, ← hcolsum, hS21] at hle
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    push_cast at hle
    linarith
  have hsum0 : (c 7 - c 0) + (c 8 - c 1) + (c 9 - c 2) = 0 := by
    have e2 := hD 7 (by omega)
    have e3 := hD 14 (by omega)
    have p := hper 0 (by omega)
    norm_num at e2 e3 p
    linarith
  have hzero : c 7 - c 0 = 0 ∧ c 8 - c 1 = 0 ∧ c 9 - c 2 = 0 := by
    generalize c 7 - c 0 = x at hΔ hsum0 ⊢
    generalize c 8 - c 1 = y at hΔ hsum0 ⊢
    generalize c 9 - c 2 = z at hΔ hsum0 ⊢
    have hz : z = -x - y := by linarith
    subst hz
    have h14 : 14 * (x ^ 2 + x * y + y ^ 2) ≤ 12 := by nlinarith
    have hq : x ^ 2 + x * y + y ^ 2 ≤ 0 := by omega
    have hy2 : y ^ 2 ≤ 0 := by nlinarith [sq_nonneg (2 * x + y)]
    have hy : y = 0 := (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hy2 (sq_nonneg y))
    subst hy
    have hx2 : x ^ 2 ≤ 0 := by nlinarith
    have hx : x = 0 := (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hx2 (sq_nonneg x))
    subst hx
    norm_num
  have hp7 : ∀ r, r < 3 → c (r + 7) = c r := by
    intro r hr
    interval_cases r <;> norm_num <;> omega
  have hcolc : ∀ b, b < 7 → c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2 = 3 * c b ^ 2 := by
    intro b hb
    have e1 := hD b (by omega)
    have e2 := hD (b + 7) (by omega)
    rw [show b + 7 + 7 = b + 14 by omega] at e2
    rw [hp7 (b % 3) (Nat.mod_lt _ (by norm_num))] at e1
    rw [hp7 ((b + 7) % 3) (Nat.mod_lt _ (by norm_num))] at e2
    have h1 : c (b + 7) = c b := by linarith
    have h2 : c (b + 14) = c b := by linarith
    rw [h1, h2]
    ring
  have h3 : ∑ b ∈ Finset.range 7, (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2) =
      3 * ∑ b ∈ Finset.range 7, c b ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b hb => hcolc b (Finset.mem_range.mp hb)
  rw [hcolsum, h3] at hS21
  omega

end GlobalTheory
