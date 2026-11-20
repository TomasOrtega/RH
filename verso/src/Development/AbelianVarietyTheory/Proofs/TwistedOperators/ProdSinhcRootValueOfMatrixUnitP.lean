import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU.RootProd

/- English proof (translation)
Unfold `shc`. Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Rewrite using `[if_neg (neg_ne_zero.mpr hx), if_neg hx, Real.sinh_neg, neg_div_neg_eq]`.
-/
theorem shc_neg' (x : ℝ) : shc (-x) = shc x := by
  unfold shc
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg (neg_ne_zero.mpr hx), if_neg hx, Real.sinh_neg, neg_div_neg_eq]

/- English proof (translation)
Unfold `shc`. Conclude with `if_pos rfl`.
-/
theorem shc_zero' : shc 0 = 1 := by
  unfold shc
  exact if_pos rfl

/- English proof (translation)
Establish `split3 : ∀ i j, F i j = (if j = i then F i i else 1) * (if i < j then F i j else 1) * (if j < i then F i j else 1)`. Introduce `i j`. Break down `lt_trichotomy i j with hij | rfl | hji` into its components or cases. Simplify using `[hij, hij.ne', not_lt.mpr hij.le]`. Simplify using the standard rewrite rules.

Simplify using `[hji, hji.ne, not_lt.mpr hji.le]`. Establish `row : ∀ i ∈ Finset.range n, (∏ j ∈ Finset.range n, F i j) = F i i * ((∏ j ∈ Finset.range n, if i < j then F i j else 1) * ∏ j ∈ Finset.range n, if j < i then F i j else 1)`. Introduce `i hi`. Establish `hd : (∏ j ∈ Finset.range n, if j = i then F i i else 1) = F i i`. Rewrite using `[Finset.prod_ite_eq']`.

Conclude with `if_pos hi`. Rewrite using `[← Finset.prod_mul_distrib, ← hd, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun j _ => by rw [← mul_assoc]; exact split3 i j`. Establish `below : (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, if j < i then F i j else 1) = ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, if i < j then F j i else 1` using `Finset.prod_comm`. Rewrite using `[Finset.prod_congr rfl row, Finset.prod_mul_distrib, Finset.prod_mul_distrib, below, ← Finset.prod_mul_distrib]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem prod_square (n : ℕ) (F : ℕ → ℕ → ℝ) :
    ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, F i j =
      (∏ i ∈ Finset.range n, F i i) *
        ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, if i < j then F i j * F j i else 1 := by

  have split3 : ∀ i j, F i j = (if j = i then F i i else 1) * (if i < j then F i j else 1) *
      (if j < i then F i j else 1) := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [hij, hij.ne', not_lt.mpr hij.le]
    · simp
    · simp [hji, hji.ne, not_lt.mpr hji.le]
  have row : ∀ i ∈ Finset.range n, (∏ j ∈ Finset.range n, F i j) =
      F i i * ((∏ j ∈ Finset.range n, if i < j then F i j else 1) *
        ∏ j ∈ Finset.range n, if j < i then F i j else 1) := by
    intro i hi
    have hd : (∏ j ∈ Finset.range n, if j = i then F i i else 1) = F i i := by
      rw [Finset.prod_ite_eq']
      exact if_pos hi
    rw [← Finset.prod_mul_distrib, ← hd, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [← mul_assoc]; exact split3 i j

  have below : (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, if j < i then F i j else 1) =
      ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, if i < j then F j i else 1 :=
    Finset.prod_comm
  rw [Finset.prod_congr rfl row, Finset.prod_mul_distrib, Finset.prod_mul_distrib, below,
    ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[← Finset.prod_subtype (Finset.univ.filter fun ab : Ix p q × Ix p q => ¬ sameBlock ab.1 ab.2) (fun ab => by simp) (fun ab => shc (rootP h ab))]`. Rewrite using `[Finset.prod_filter, Fintype.prod_prod_type]`. Simplify using `only [Fintype.prod_sum_type, sameBlock, not_true_eq_false, not_false_eq_true, if_false, if_true, Finset.prod_const_one, one_mul, mul_one, rootP, Sum.isLeft_inl, Sum.isLeft_inr, posIx, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true]`. Repeatedly rewrite using `[Finset.prod_range, Finset.prod_mul_distrib]`. Use `congr 1`.

Rewrite using `[Finset.prod_comm]`. Conclude with `Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by rw [add_comm]`.
-/
theorem prod_PIx (p q : ℕ) (h : ℕ → ℝ) :
    ∏ ab : PIx p q, shc (rootP h ab.1) =
      ∏ i ∈ Finset.range p, ∏ j ∈ Finset.range q,
        shc (cutH p q h i - cutH p q h j) * shc (cutH p q h i + cutH p q h j) := by

  rw [← Finset.prod_subtype (Finset.univ.filter fun ab : Ix p q × Ix p q => ¬ sameBlock ab.1 ab.2)
    (fun ab => by simp) (fun ab => shc (rootP h ab))]
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  simp only [Fintype.prod_sum_type, sameBlock, not_true_eq_false, not_false_eq_true, if_false,
    if_true, Finset.prod_const_one, one_mul, mul_one, rootP, Sum.isLeft_inl, Sum.isLeft_inr,
    posIx, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true]
  simp_rw [Finset.prod_range, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by rw [add_comm]

/- English proof (translation)
Establish `hin : ∀ i ∈ Finset.range m, c i = h i` using `fun i hi => by`. Rewrite using `[hc, if_pos (Finset.mem_range.mp hi)]`. Establish `hout : ∀ k, c (m + k) = 0` using `fun k => by`. Rewrite using `[hc, if_neg (by omega)]`. Establish `swap : ∀ a b : ℝ, shc (b - a) * shc (b + a) = shc (a - b) * shc (a + b)` using `fun a b => by`.

Rewrite using `[show b - a = -(a - b) by ring, shc_neg', add_comm b a]`. Establish `row : ∀ i ∈ Finset.range m, (∏ j ∈ Finset.range (m + d), shc (c i - c j) * shc (c i + c j)) = (∏ j ∈ Finset.range m, shc (h i - h j) * shc (h i + h j)) * shc (h i) ^ (2 * d)`. Introduce `i hi`. Rewrite using `[Finset.prod_range_add]`. Use `congr 1`.

Conclude with `Finset.prod_congr rfl fun j hj => by rw [hin i hi, hin j hj]`. Simplify using `only [hout, hin i hi, sub_zero, add_zero]`. Rewrite using `[Finset.prod_const, Finset.card_range, ← pow_two, ← pow_mul]`. Establish `diag : ∀ i, shc (h i - h i) * shc (h i + h i) = shc (2 * h i)` using `fun i => by`. Rewrite using `[sub_self, shc_zero', one_mul, two_mul]`.

Establish `off : ∀ i j, (if i < j then shc (h i - h j) * shc (h i + h j) * (shc (h j - h i) * shc (h j + h i)) else 1) = if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1` using `fun i j => by`. Rewrite using `[swap (h i) (h j), sq]`. Rewrite using `[Finset.prod_congr rfl row, Finset.prod_mul_distrib, prod_square m (fun i j => shc (h i - h j) * shc (h i + h j))]`. Simplify using `only [diag]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => off i j]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_rect (m d : ℕ) (h c : ℕ → ℝ) (hc : ∀ n, c n = if n < m then h n else 0) :
    ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range (m + d), shc (c i - c j) * shc (c i + c j) =
      (∏ i ∈ Finset.range m, shc (2 * h i) * shc (h i) ^ (2 * d)) *
        ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m,
          if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1 := by
  have hin : ∀ i ∈ Finset.range m, c i = h i := fun i hi => by
    rw [hc, if_pos (Finset.mem_range.mp hi)]
  have hout : ∀ k, c (m + k) = 0 := fun k => by
    rw [hc, if_neg (by omega)]

  have swap : ∀ a b : ℝ, shc (b - a) * shc (b + a) = shc (a - b) * shc (a + b) := fun a b => by
    rw [show b - a = -(a - b) by ring, shc_neg', add_comm b a]

  have row : ∀ i ∈ Finset.range m,
      (∏ j ∈ Finset.range (m + d), shc (c i - c j) * shc (c i + c j)) =
        (∏ j ∈ Finset.range m, shc (h i - h j) * shc (h i + h j)) * shc (h i) ^ (2 * d) := by
    intro i hi
    rw [Finset.prod_range_add]
    congr 1
    · exact Finset.prod_congr rfl fun j hj => by rw [hin i hi, hin j hj]
    · simp only [hout, hin i hi, sub_zero, add_zero]
      rw [Finset.prod_const, Finset.card_range, ← pow_two, ← pow_mul]
  have diag : ∀ i, shc (h i - h i) * shc (h i + h i) = shc (2 * h i) := fun i => by
    rw [sub_self, shc_zero', one_mul, two_mul]
  have off : ∀ i j, (if i < j then shc (h i - h j) * shc (h i + h j) * (shc (h j - h i) * shc (h j + h i))
      else 1) = if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1 := fun i j => by
    rw [swap (h i) (h j), sq]
  rw [Finset.prod_congr rfl row, Finset.prod_mul_distrib,
    prod_square m (fun i j => shc (h i - h j) * shc (h i + h j))]
  simp only [diag]
  rw [Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => off i j]
  ring

/- English proof (translation)
Introduce `p q h`. Establish `hm : min p q + (max p q - min p q) = max p q` using `Nat.add_sub_cancel' min_le_max`. Establish `swap : ∀ a b : ℝ, shc (b - a) * shc (b + a) = shc (a - b) * shc (a + b)` using `fun a b => by`. Rewrite using `[show b - a = -(a - b) by ring, shc_neg', add_comm b a]`. Rewrite using `[← prod_rect (min p q) (max p q - min p q) h (cutH p q h) (fun n => rfl), hm, prod_PIx]`.

Break down `le_total p q with hpq | hqp` into its components or cases. Rewrite using `[min_eq_left hpq, max_eq_right hpq]`. Rewrite using `[min_eq_right hqp, max_eq_left hqp, Finset.prod_comm]`. Conclude with `Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => swap _ _`.
-/
theorem prod_shc_rootP : ∀ (p q : ℕ) (h : ℕ → ℝ), ∏ ab : PIx p q, shc (rootP h ab.1) = (∏ i ∈ Finset.range (min p q), shc (2 * h i) * shc (h i) ^ (2 * (max p q - min p q))) * ∏ i ∈ Finset.range (min p q), ∏ j ∈ Finset.range (min p q), if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1 := by
  intro p q h
  have hm : min p q + (max p q - min p q) = max p q := Nat.add_sub_cancel' min_le_max
  have swap : ∀ a b : ℝ, shc (b - a) * shc (b + a) = shc (a - b) * shc (a + b) := fun a b => by
    rw [show b - a = -(a - b) by ring, shc_neg', add_comm b a]
  rw [← prod_rect (min p q) (max p q - min p q) h (cutH p q h) (fun n => rfl), hm, prod_PIx]
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq, max_eq_right hpq]
  ·
    rw [min_eq_right hqp, max_eq_left hqp, Finset.prod_comm]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => swap _ _

end GlobalTheory.PolarU.RootProd
