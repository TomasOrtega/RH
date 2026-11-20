import Mathlib

open Finset

namespace UpperTheory.Zero.LLC.CharacterSumPairs

def bd (g n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, (g ^ (n / p) - 1)

/- English proof (translation)
Proceed by induction on `M with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[Finset.sum_range_succ, pow_succ]`. Combine the linear relations using `[ih, Nat.mul_le_mul_left (g ^ k) hg]`.
-/
private theorem geom (g : ℕ) (hg : 2 ≤ g) (M : ℕ) : ∑ d ∈ range (M + 1), g ^ d ≤ 2 * g ^ M := by
  induction M with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith [ih, Nat.mul_le_mul_left (g ^ k) hg]

/- English proof (translation)
Unfold `bd`. Establish `hsub : ∑ p ∈ n.primeFactors, (g ^ (n / p) - 1) ≤ ∑ p ∈ n.primeFactors, g ^ (n / p)` using `Finset.sum_le_sum fun p _ => Nat.sub_le _ _`. Establish `hinj : Set.InjOn (fun p => n / p) (n.primeFactors : Set ℕ)`. Introduce `p hp q hq hpq`. Establish `hp'` using `Nat.dvd_of_mem_primeFactors hp`.

Establish `hq'` using `Nat.dvd_of_mem_primeFactors hq`. Simplify using `only at hpq`. Rewrite using `[← Nat.div_div_self hp' hn.ne', hpq, Nat.div_div_self hq' hn.ne']`. Establish `himg : ∑ p ∈ n.primeFactors, g ^ (n / p) = ∑ d ∈ n.primeFactors.image (fun p => n / p), g ^ d` using `(Finset.sum_image hinj).symm`. Establish `hsubset : n.primeFactors.image (fun p => n / p) ⊆ range (n / 2 + 1)`.

Introduce `d hd`. Rewrite `hd` using `[Finset.mem_image]`. Take `⟨p, hp, rfl⟩` from `hd`. Rewrite using `[Finset.mem_range, Nat.lt_succ_iff]`. Conclude with `Nat.div_le_div_left (Nat.prime_of_mem_primeFactors hp).two_le (by norm_num)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem bd_le (g n : ℕ) (hg : 2 ≤ g) (hn : 0 < n) : bd g n ≤ 2 * g ^ (n / 2) := by
  unfold bd
  have hsub : ∑ p ∈ n.primeFactors, (g ^ (n / p) - 1) ≤ ∑ p ∈ n.primeFactors, g ^ (n / p) :=
    Finset.sum_le_sum fun p _ => Nat.sub_le _ _
  have hinj : Set.InjOn (fun p => n / p) (n.primeFactors : Set ℕ) := by
    intro p hp q hq hpq
    have hp' := Nat.dvd_of_mem_primeFactors hp
    have hq' := Nat.dvd_of_mem_primeFactors hq
    simp only at hpq
    rw [← Nat.div_div_self hp' hn.ne', hpq, Nat.div_div_self hq' hn.ne']
  have himg : ∑ p ∈ n.primeFactors, g ^ (n / p)
      = ∑ d ∈ n.primeFactors.image (fun p => n / p), g ^ d :=
    (Finset.sum_image hinj).symm
  have hsubset : n.primeFactors.image (fun p => n / p) ⊆ range (n / 2 + 1) := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨p, hp, rfl⟩ := hd
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_left (Nat.prime_of_mem_primeFactors hp).two_le (by norm_num)
  calc _ ≤ _ := hsub
    _ = _ := himg
    _ ≤ ∑ d ∈ range (n / 2 + 1), g ^ d := Finset.sum_le_sum_of_subset hsubset
    _ ≤ 2 * g ^ (n / 2) := geom g hg (n / 2)

/- English proof (translation)
Proceed by induction on `m, hm using Nat.le_induction with`. Consider the case `base => norm_num`. Consider the case `succ m hm ih`. Rewrite using `[pow_succ]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem two_pow (m : ℕ) (hm : 6 ≤ m) : 8 * m + 1 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    omega

/- English proof (translation)
Take `⟨m, rfl | rfl⟩` from `Nat.even_or_odd' n`. Establish `hm : 6 ≤ m` using `by omega`. Establish `hb` using `bd_le g (2 * m) hg (by omega)`. Rewrite `hb` using `[Nat.mul_div_cancel_left m (by norm_num : 0 < 2)]`. Establish `hA : 8 * m + 1 ≤ g ^ m` using `le_trans (two_pow m hm) (Nat.pow_le_pow_left hg m)`.

Establish `hp : g ^ (2 * m) = g ^ m * g ^ m` using `by rw [two_mul, pow_add]`. Rewrite using `[hp]`. Generalize the expression as in `bd g (2 * m) = B at hb ⊢`. Generalize the expression as in `g ^ m = A at hA hb ⊢`. Use polynomial arithmetic with `[Nat.mul_le_mul_left m hb, Nat.mul_le_mul_left A hA]`.

Establish `hm : 6 ≤ m` using `by omega`. Establish `hb` using `bd_le g (2 * m + 1) hg (by omega)`. Establish `hd : (2 * m + 1) / 2 = m` using `by omega`. Rewrite `hb` using `[hd]`. Establish `hA : 8 * m + 1 ≤ g ^ m` using `le_trans (two_pow m hm) (Nat.pow_le_pow_left hg m)`.

Establish `hp : g ^ (2 * m + 1) = g ^ m * g ^ m * g` using `by rw [pow_succ, two_mul, pow_add]`. Rewrite using `[hp]`. Generalize the expression as in `bd g (2 * m + 1) = B at hb ⊢`. Generalize the expression as in `g ^ m = A at hA hb ⊢`. Use polynomial arithmetic with `[Nat.mul_le_mul_left m hb, Nat.mul_le_mul_left A hA, Nat.mul_le_mul_left (A * A) hg, Nat.mul_le_mul_right A hm]`.
-/
theorem big (g n : ℕ) (hg : 2 ≤ g) (hn : 12 ≤ n) : 2 * n * bd g n + 1 < g ^ n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hm : 6 ≤ m := by omega
    have hb := bd_le g (2 * m) hg (by omega)
    rw [Nat.mul_div_cancel_left m (by norm_num : 0 < 2)] at hb
    have hA : 8 * m + 1 ≤ g ^ m := le_trans (two_pow m hm) (Nat.pow_le_pow_left hg m)
    have hp : g ^ (2 * m) = g ^ m * g ^ m := by rw [two_mul, pow_add]
    rw [hp]
    generalize bd g (2 * m) = B at hb ⊢
    generalize g ^ m = A at hA hb ⊢
    nlinarith [Nat.mul_le_mul_left m hb, Nat.mul_le_mul_left A hA]
  · have hm : 6 ≤ m := by omega
    have hb := bd_le g (2 * m + 1) hg (by omega)
    have hd : (2 * m + 1) / 2 = m := by omega
    rw [hd] at hb
    have hA : 8 * m + 1 ≤ g ^ m := le_trans (two_pow m hm) (Nat.pow_le_pow_left hg m)
    have hp : g ^ (2 * m + 1) = g ^ m * g ^ m * g := by rw [pow_succ, two_mul, pow_add]
    rw [hp]
    generalize bd g (2 * m + 1) = B at hb ⊢
    generalize g ^ m = A at hA hb ⊢
    nlinarith [Nat.mul_le_mul_left m hb, Nat.mul_le_mul_left A hA, Nat.mul_le_mul_left (A * A) hg,
      Nat.mul_le_mul_right A hm]

/- English proof (translation)
Evaluate the numerical expressions using `[Nat.primeFactors, Nat.primeFactorsList]`.
-/
private theorem pf2 : Nat.primeFactors 2 = {2} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]
/- English proof (translation)
Evaluate the numerical expressions using `[Nat.primeFactors, Nat.primeFactorsList]`.
-/
private theorem pf3 : Nat.primeFactors 3 = {3} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]
/- English proof (translation)
Evaluate the numerical expressions using `[Nat.primeFactors, Nat.primeFactorsList]`.
-/
private theorem pf4 : Nat.primeFactors 4 = {2} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]
/- English proof (translation)
Evaluate the numerical expressions using `[Nat.primeFactors, Nat.primeFactorsList]`.
-/
private theorem pf5 : Nat.primeFactors 5 = {5} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]
/- English proof (translation)
Evaluate the numerical expressions using `[Nat.primeFactors, Nat.primeFactorsList]`.
-/
private theorem pf6 : Nat.primeFactors 6 = {2, 3} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]
/- English proof (translation)
Evaluate the numerical expressions using `[Nat.primeFactors, Nat.primeFactorsList]`.
-/
private theorem pf7 : Nat.primeFactors 7 = {7} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]
/- English proof (translation)
Evaluate the numerical expressions using `[Nat.primeFactors, Nat.primeFactorsList]`.
-/
private theorem pf8 : Nat.primeFactors 8 = {2} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]
/- English proof (translation)
Evaluate the numerical expressions using `[Nat.primeFactors, Nat.primeFactorsList]`.
-/
private theorem pf9 : Nat.primeFactors 9 = {3} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]
/- English proof (translation)
Evaluate the numerical expressions using `[Nat.primeFactors, Nat.primeFactorsList]`.
-/
private theorem pf10 : Nat.primeFactors 10 = {2, 5} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]
/- English proof (translation)
Evaluate the numerical expressions using `[Nat.primeFactors, Nat.primeFactorsList]`.
-/
private theorem pf11 : Nat.primeFactors 11 = {11} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]

/- English proof (translation)
Simplify using `[bd, pf2]`.
-/
theorem bd_two (g : ℕ) : bd g 2 = g - 1 := by simp [bd, pf2]
/- English proof (translation)
Simplify using `[bd, pf3]`.
-/
theorem bd_three (g : ℕ) : bd g 3 = g - 1 := by simp [bd, pf3]
/- English proof (translation)
Simplify using `[bd, pf4]`.
-/
theorem bd_four (g : ℕ) : bd g 4 = g ^ 2 - 1 := by simp [bd, pf4]
/- English proof (translation)
Simplify using `[bd, pf5]`.
-/
theorem bd_five (g : ℕ) : bd g 5 = g - 1 := by simp [bd, pf5]
/- English proof (translation)
Simplify using `[bd, pf6]`.
-/
theorem bd_six (g : ℕ) : bd g 6 = (g ^ 3 - 1) + (g ^ 2 - 1) := by simp [bd, pf6]
/- English proof (translation)
Simplify using `[bd, pf7]`.
-/
theorem bd_seven (g : ℕ) : bd g 7 = g - 1 := by simp [bd, pf7]
/- English proof (translation)
Simplify using `[bd, pf8]`.
-/
theorem bd_eight (g : ℕ) : bd g 8 = g ^ 4 - 1 := by simp [bd, pf8]
/- English proof (translation)
Simplify using `[bd, pf9]`.
-/
theorem bd_nine (g : ℕ) : bd g 9 = g ^ 3 - 1 := by simp [bd, pf9]
/- English proof (translation)
Simplify using `[bd, pf10]`.
-/
theorem bd_ten (g : ℕ) : bd g 10 = (g ^ 5 - 1) + (g ^ 2 - 1) := by simp [bd, pf10]
/- English proof (translation)
Simplify using `[bd, pf11]`.
-/
theorem bd_eleven (g : ℕ) : bd g 11 = g - 1 := by simp [bd, pf11]

/- English proof (translation)
Establish `h1 : 1 ≤ (h + c) ^ k` using `Nat.one_le_pow _ _ (by omega)`. Rewrite using `[Nat.cast_sub h1, Nat.cast_pow, Nat.cast_add, Nat.cast_one]`.
-/
private theorem cast_pred (h c k : ℕ) (hc : 1 ≤ c) : (((h + c) ^ k - 1 : ℕ) : ℤ) = ((h : ℤ) + c) ^ k - 1 := by
  have h1 : 1 ≤ (h + c) ^ k := Nat.one_le_pow _ _ (by omega)
  rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_add, Nat.cast_one]

/- English proof (translation)
Rewrite using `[Nat.cast_sub (by omega : 1 ≤ h + c), Nat.cast_add, Nat.cast_one]`.
-/
private theorem cast_pred1 (h c : ℕ) (hc : 1 ≤ c) : (((h + c) - 1 : ℕ) : ℤ) = ((h : ℤ) + c) - 1 := by
  rw [Nat.cast_sub (by omega : 1 ≤ h + c), Nat.cast_add, Nat.cast_one]

/- English proof (translation)
Rewrite using `[bd_two]`. Establish `e0` using `cast_pred1 h 4 (by norm_num)`. Establish `key : ((2 * 2 * ((h + 4 - 1)) + 1 : ℕ) : ℤ) < (((h + 4) ^ 2 : ℕ) : ℤ)`. Rewrite using `[Nat.cast_add, Nat.cast_mul, e0]`. Use `push_cast`.

Rewrite using `[← sub_pos]`. Put the polynomial expressions in normal form. Check the signs of the components of the expression. Conclude with `Nat.cast_lt.mp key`.
-/
private theorem t2 (h : ℕ) : 2 * 2 * bd (h + 4) 2 + 1 < (h + 4) ^ 2 := by
  rw [bd_two]
  have e0 := cast_pred1 h 4 (by norm_num)
  have key : ((2 * 2 * ((h + 4 - 1)) + 1 : ℕ) : ℤ) < (((h + 4) ^ 2 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

/- English proof (translation)
Rewrite using `[bd_three]`. Establish `e0` using `cast_pred1 h 2 (by norm_num)`. Establish `key : ((2 * 3 * ((h + 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 3 : ℕ) : ℤ)`. Rewrite using `[Nat.cast_add, Nat.cast_mul, e0]`. Use `push_cast`.

Rewrite using `[← sub_pos]`. Put the polynomial expressions in normal form. Check the signs of the components of the expression. Conclude with `Nat.cast_lt.mp key`.
-/
private theorem t3 (h : ℕ) : 2 * 3 * bd (h + 2) 3 + 1 < (h + 2) ^ 3 := by
  rw [bd_three]
  have e0 := cast_pred1 h 2 (by norm_num)
  have key : ((2 * 3 * ((h + 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 3 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

/- English proof (translation)
Rewrite using `[bd_four]`. Establish `e0` using `cast_pred h 3 2 (by norm_num)`. Establish `key : ((2 * 4 * (((h + 3) ^ 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 3) ^ 4 : ℕ) : ℤ)`. Rewrite using `[Nat.cast_add, Nat.cast_mul, e0]`. Use `push_cast`.

Rewrite using `[← sub_pos]`. Put the polynomial expressions in normal form. Check the signs of the components of the expression. Conclude with `Nat.cast_lt.mp key`.
-/
private theorem t4 (h : ℕ) : 2 * 4 * bd (h + 3) 4 + 1 < (h + 3) ^ 4 := by
  rw [bd_four]
  have e0 := cast_pred h 3 2 (by norm_num)
  have key : ((2 * 4 * (((h + 3) ^ 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 3) ^ 4 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

/- English proof (translation)
Rewrite using `[bd_five]`. Establish `e0` using `cast_pred1 h 2 (by norm_num)`. Establish `key : ((2 * 5 * ((h + 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 5 : ℕ) : ℤ)`. Rewrite using `[Nat.cast_add, Nat.cast_mul, e0]`. Use `push_cast`.

Rewrite using `[← sub_pos]`. Put the polynomial expressions in normal form. Check the signs of the components of the expression. Conclude with `Nat.cast_lt.mp key`.
-/
private theorem t5 (h : ℕ) : 2 * 5 * bd (h + 2) 5 + 1 < (h + 2) ^ 5 := by
  rw [bd_five]
  have e0 := cast_pred1 h 2 (by norm_num)
  have key : ((2 * 5 * ((h + 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 5 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

/- English proof (translation)
Rewrite using `[bd_six]`. Establish `e0` using `cast_pred h 3 3 (by norm_num)`. Establish `e1` using `cast_pred h 3 2 (by norm_num)`. Establish `key : ((2 * 6 * (((h + 3) ^ 3 - 1) + ((h + 3) ^ 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 3) ^ 6 : ℕ) : ℤ)`. Rewrite using `[Nat.cast_add, Nat.cast_mul, Nat.cast_add, e0, e1]`.

Use `push_cast`. Rewrite using `[← sub_pos]`. Put the polynomial expressions in normal form. Check the signs of the components of the expression. Conclude with `Nat.cast_lt.mp key`.
-/
private theorem t6 (h : ℕ) : 2 * 6 * bd (h + 3) 6 + 1 < (h + 3) ^ 6 := by
  rw [bd_six]
  have e0 := cast_pred h 3 3 (by norm_num)
  have e1 := cast_pred h 3 2 (by norm_num)
  have key : ((2 * 6 * (((h + 3) ^ 3 - 1) + ((h + 3) ^ 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 3) ^ 6 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, e0, e1]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

/- English proof (translation)
Rewrite using `[bd_seven]`. Establish `e0` using `cast_pred1 h 2 (by norm_num)`. Establish `key : ((2 * 7 * ((h + 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 7 : ℕ) : ℤ)`. Rewrite using `[Nat.cast_add, Nat.cast_mul, e0]`. Use `push_cast`.

Rewrite using `[← sub_pos]`. Put the polynomial expressions in normal form. Check the signs of the components of the expression. Conclude with `Nat.cast_lt.mp key`.
-/
private theorem t7 (h : ℕ) : 2 * 7 * bd (h + 2) 7 + 1 < (h + 2) ^ 7 := by
  rw [bd_seven]
  have e0 := cast_pred1 h 2 (by norm_num)
  have key : ((2 * 7 * ((h + 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 7 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

/- English proof (translation)
Rewrite using `[bd_eight]`. Establish `e0` using `cast_pred h 2 4 (by norm_num)`. Establish `key : ((2 * 8 * (((h + 2) ^ 4 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 8 : ℕ) : ℤ)`. Rewrite using `[Nat.cast_add, Nat.cast_mul, e0]`. Use `push_cast`.

Rewrite using `[← sub_pos]`. Put the polynomial expressions in normal form. Check the signs of the components of the expression. Conclude with `Nat.cast_lt.mp key`.
-/
private theorem t8 (h : ℕ) : 2 * 8 * bd (h + 2) 8 + 1 < (h + 2) ^ 8 := by
  rw [bd_eight]
  have e0 := cast_pred h 2 4 (by norm_num)
  have key : ((2 * 8 * (((h + 2) ^ 4 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 8 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

/- English proof (translation)
Rewrite using `[bd_nine]`. Establish `e0` using `cast_pred h 2 3 (by norm_num)`. Establish `key : ((2 * 9 * (((h + 2) ^ 3 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 9 : ℕ) : ℤ)`. Rewrite using `[Nat.cast_add, Nat.cast_mul, e0]`. Use `push_cast`.

Rewrite using `[← sub_pos]`. Put the polynomial expressions in normal form. Check the signs of the components of the expression. Conclude with `Nat.cast_lt.mp key`.
-/
private theorem t9 (h : ℕ) : 2 * 9 * bd (h + 2) 9 + 1 < (h + 2) ^ 9 := by
  rw [bd_nine]
  have e0 := cast_pred h 2 3 (by norm_num)
  have key : ((2 * 9 * (((h + 2) ^ 3 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 9 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

/- English proof (translation)
Rewrite using `[bd_ten]`. Establish `e0` using `cast_pred h 2 5 (by norm_num)`. Establish `e1` using `cast_pred h 2 2 (by norm_num)`. Establish `key : ((2 * 10 * (((h + 2) ^ 5 - 1) + ((h + 2) ^ 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 10 : ℕ) : ℤ)`. Rewrite using `[Nat.cast_add, Nat.cast_mul, Nat.cast_add, e0, e1]`.

Use `push_cast`. Rewrite using `[← sub_pos]`. Put the polynomial expressions in normal form. Check the signs of the components of the expression. Conclude with `Nat.cast_lt.mp key`.
-/
private theorem t10 (h : ℕ) : 2 * 10 * bd (h + 2) 10 + 1 < (h + 2) ^ 10 := by
  rw [bd_ten]
  have e0 := cast_pred h 2 5 (by norm_num)
  have e1 := cast_pred h 2 2 (by norm_num)
  have key : ((2 * 10 * (((h + 2) ^ 5 - 1) + ((h + 2) ^ 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 10 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, e0, e1]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

/- English proof (translation)
Rewrite using `[bd_eleven]`. Establish `e0` using `cast_pred1 h 2 (by norm_num)`. Establish `key : ((2 * 11 * ((h + 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 11 : ℕ) : ℤ)`. Rewrite using `[Nat.cast_add, Nat.cast_mul, e0]`. Use `push_cast`.

Rewrite using `[← sub_pos]`. Put the polynomial expressions in normal form. Check the signs of the components of the expression. Conclude with `Nat.cast_lt.mp key`.
-/
private theorem t11 (h : ℕ) : 2 * 11 * bd (h + 2) 11 + 1 < (h + 2) ^ 11 := by
  rw [bd_eleven]
  have e0 := cast_pred1 h 2 (by norm_num)
  have key : ((2 * 11 * ((h + 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 11 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

/- English proof (translation)
Break down `le_or_gt 12 n with h12 | h12` into its components or cases. Conclude with `big g n hg h12`. Use `interval_cases n`. Simplify using `[bd]`. Use linear arithmetic over natural numbers and integers.

Take `⟨k, rfl⟩ : ∃ k, g = k + 4` from `⟨g - 4, by omega⟩`. Conclude with `t2 k`. Take `⟨k, rfl⟩ : ∃ k, g = k + 2` from `⟨g - 2, by omega⟩`. Conclude with `t3 k`. Take `⟨k, rfl⟩ : ∃ k, g = k + 3` from `⟨g - 3, by omega⟩`.

Conclude with `t4 k`. Take `⟨k, rfl⟩ : ∃ k, g = k + 2` from `⟨g - 2, by omega⟩`. Conclude with `t5 k`. Take `⟨k, rfl⟩ : ∃ k, g = k + 3` from `⟨g - 3, by omega⟩`. Conclude with `t6 k`.

Take `⟨k, rfl⟩ : ∃ k, g = k + 2` from `⟨g - 2, by omega⟩`. Conclude with `t7 k`. Take `⟨k, rfl⟩ : ∃ k, g = k + 2` from `⟨g - 2, by omega⟩`. Conclude with `t8 k`. Take `⟨k, rfl⟩ : ∃ k, g = k + 2` from `⟨g - 2, by omega⟩`.

Conclude with `t9 k`. Take `⟨k, rfl⟩ : ∃ k, g = k + 2` from `⟨g - 2, by omega⟩`. Conclude with `t10 k`. Take `⟨k, rfl⟩ : ∃ k, g = k + 2` from `⟨g - 2, by omega⟩`. Conclude with `t11 k`.
-/
theorem two_bd (g n : ℕ) (hg : 2 ≤ g) (hn : 0 < n)
    (hex : ¬ ((g = 2 ∧ n = 2) ∨ (g = 3 ∧ n = 2) ∨ (g = 2 ∧ n = 4) ∨ (g = 2 ∧ n = 6))) :
    2 * n * bd g n + 1 < g ^ n := by
  rcases le_or_gt 12 n with h12 | h12
  · exact big g n hg h12
  · interval_cases n
    · simp [bd]
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 4 := ⟨g - 4, by omega⟩
      exact t2 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t3 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 3 := ⟨g - 3, by omega⟩
      exact t4 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t5 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 3 := ⟨g - 3, by omega⟩
      exact t6 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t7 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t8 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t9 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t10 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t11 k

/- English proof (translation)
Distinguish the cases in `hex : (g = 2 ∧ n = 2) ∨ (g = 3 ∧ n = 2) ∨ (g = 2 ∧ n = 4) ∨ (g = 2 ∧ n = 6)`. Break down `hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases. Rewrite using `[bd_two]`. Evaluate the numerical expressions. Rewrite using `[bd_two]`.

Evaluate the numerical expressions. Rewrite using `[bd_four]`. Evaluate the numerical expressions. Rewrite using `[bd_six]`. Evaluate the numerical expressions.

Establish `h2` using `two_bd g n hg hn hex`. Combine the linear relations using `[Nat.mul_le_mul_right (bd g n) (show n ≤ 2 * n by omega)]`.
-/
theorem one_bd (g n : ℕ) (hg : 2 ≤ g) (hn : 0 < n) : n * bd g n + 1 < g ^ n := by
  by_cases hex : (g = 2 ∧ n = 2) ∨ (g = 3 ∧ n = 2) ∨ (g = 2 ∧ n = 4) ∨ (g = 2 ∧ n = 6)
  · rcases hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [bd_two]
      norm_num
    · rw [bd_two]
      norm_num
    · rw [bd_four]
      norm_num
    · rw [bd_six]
      norm_num
  · have h2 := two_bd g n hg hn hex
    linarith [Nat.mul_le_mul_right (bd g n) (show n ≤ 2 * n by omega)]

end UpperTheory.Zero.LLC.CharacterSumPairs
