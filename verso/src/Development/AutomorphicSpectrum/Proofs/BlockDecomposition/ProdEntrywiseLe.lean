import Mathlib

open Finset

namespace GlobalTheory.CompanionTheory.EntrywiseCount

/- English proof (translation)
Establish `h : (univ.filter (fun i : Fin n => (i : ℕ) < r)).card = ((range n).filter (fun i => i < r)).card`. Rewrite using `[Finset.card_filter, Finset.card_filter]`. Conclude with `Fin.sum_univ_eq_sum_range (fun i => if i < r then 1 else 0) n`. Rewrite using `[h]`. Establish `: (range n).filter (fun i => i < r) = range r`.

Use extensionality with `x`. Simplify using `only [mem_filter, mem_range]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[this, card_range]`.
-/
theorem card_lt (n r : ℕ) (hr : r ≤ n) :
    (univ.filter (fun i : Fin n => (i : ℕ) < r)).card = r := by
  have h : (univ.filter (fun i : Fin n => (i : ℕ) < r)).card
      = ((range n).filter (fun i => i < r)).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Fin.sum_univ_eq_sum_range (fun i => if i < r then 1 else 0) n
  rw [h]
  have : (range n).filter (fun i => i < r) = range r := by
    ext x
    simp only [mem_filter, mem_range]
    omega
  rw [this, card_range]

/- English proof (translation)
Establish `h` using `Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i : Fin n => (i : ℕ) < r)`. Rewrite `h` using `[card_lt n r hr, Finset.card_univ, Fintype.card_fin]`. Simplify using `only [not_lt] at h`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_ge (n r : ℕ) (hr : r ≤ n) :
    (univ.filter (fun j : Fin n => r ≤ (j : ℕ))).card = n - r := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i : Fin n => (i : ℕ) < r)
  rw [card_lt n r hr, Finset.card_univ, Fintype.card_fin] at h
  simp only [not_lt] at h
  omega

/- English proof (translation)
Establish `inner : ∀ i : Fin n, ∏ j : Fin n, (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then E else 1) = if (i : ℕ) < r then E ^ (n - r) else 1`. Introduce `i`. Distinguish the cases in `hi : (i : ℕ) < r`. Simplify using `only [hi, true_and, if_true]`. Rewrite using `[Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, card_ge n r hr]`.

Simplify using `[hi]`. Simplify using `only [inner]`. Rewrite using `[Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, card_lt n r hr, ← pow_mul, mul_comm]`.
-/
theorem prod_indicator (n r : ℕ) (hr : r ≤ n) (E : ℝ) :
    ∏ i : Fin n, ∏ j : Fin n, (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then E else 1)
      = E ^ (r * (n - r)) := by
  have inner : ∀ i : Fin n, ∏ j : Fin n, (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then E else 1)
      = if (i : ℕ) < r then E ^ (n - r) else 1 := by
    intro i
    by_cases hi : (i : ℕ) < r
    · simp only [hi, true_and, if_true]
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, card_ge n r hr]
    · simp [hi]
  simp only [inner]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, card_lt n r hr,
    ← pow_mul, mul_comm]

/- English proof (translation)
Establish `hE : 1 ≤ Real.exp t` using `Real.one_le_exp ht`. Establish `hbase : 1 + β * (if p then Real.exp t else 1) ≤ (1 + β) * (if p then Real.exp t else 1)` using `by split_ifs`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Apply the tactic sequence `have hnn : 0 ≤ 1 + β * (if p then Real.exp t else 1) := by split_ifs <;> positivity`.

Establish `hpow` using `pow_le_pow_left₀ hnn hbase d`. Rewrite `hpow` using `[mul_pow]`. Establish `hE' : (if p then Real.exp t else 1) ^ d = (if p then Real.exp ((d : ℝ) * t) else 1)` using `by split_ifs`. Rewrite using `[← Real.exp_nat_mul]`. Simplify using the standard rewrite rules.

Rewrite `hpow` using `[hE']`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem factor_le (d : ℕ) (C β t : ℝ) (p : Prop) [Decidable p]
    (hC : 0 ≤ C) (hβ : 0 ≤ β) (ht : 0 ≤ t) :
    C * (1 + β * (if p then Real.exp t else 1)) ^ d
      ≤ (C * (1 + β) ^ d) * (if p then Real.exp ((d : ℝ) * t) else 1) := by
  have hE : 1 ≤ Real.exp t := Real.one_le_exp ht
  have hbase : 1 + β * (if p then Real.exp t else 1)
      ≤ (1 + β) * (if p then Real.exp t else 1) := by
    split_ifs
    · nlinarith
    · linarith
  have hnn : 0 ≤ 1 + β * (if p then Real.exp t else 1) := by
    split_ifs <;> positivity
  have hpow := pow_le_pow_left₀ hnn hbase d
  rw [mul_pow] at hpow
  have hE' : (if p then Real.exp t else 1) ^ d = (if p then Real.exp ((d : ℝ) * t) else 1) := by
    split_ifs
    · rw [← Real.exp_nat_mul]
    · simp
  rw [hE'] at hpow
  calc C * (1 + β * (if p then Real.exp t else 1)) ^ d
      ≤ C * ((1 + β) ^ d * (if p then Real.exp ((d : ℝ) * t) else 1)) :=
        mul_le_mul_of_nonneg_left hpow hC
    _ = _ := by ring

/- English proof (translation)
Introduce `n r d hr C β t hC hβ ht`. Establish `hnn : ∀ (i j : Fin n), 0 ≤ C * (1 + β * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1)) ^ d`. Introduce `i j`. Apply the tactic sequence `have : 0 ≤ (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1) := by split_ifs <;> positivity`. Check the signs of the components of the expression.

Establish `step : ∏ i : Fin n, ∏ j : Fin n, C * (1 + β * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1)) ^ d ≤ ∏ i : Fin n, ∏ j : Fin n, ((C * (1 + β) ^ d) * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp ((d : ℝ) * t) else 1))`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `i _`. Conclude with `Finset.prod_nonneg (fun j _ => hnn i j)`. Introduce `i _`.

Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `j _`. Conclude with `hnn i j`. Introduce `j _`. Conclude with `factor_le d C β t _ hC hβ ht`.

Use `step.trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[prod_indicator n r hr, ← Real.exp_nat_mul, ← pow_mul]`. Establish `hp : (((1 + β) ^ d) ^ n) ^ n = (1 + β) ^ (d * (n * n))`. Rewrite using `[← pow_mul, ← pow_mul]`.

Establish `: (((r * (n - r) : ℕ) : ℝ)) * ((d : ℝ) * t) = (d : ℝ) * ((r : ℝ) * ((n : ℝ) - r)) * t`. Rewrite using `[Nat.cast_mul, Nat.cast_sub hr]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Rewrite using `[hp]`.
-/
theorem prod_entrywise_le : ∀ (n r d : ℕ), r ≤ n → ∀ (C β t : ℝ), 0 ≤ C → 0 ≤ β → 0 ≤ t →
    ∏ i : Fin n, ∏ j : Fin n,
        C * (1 + β * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1)) ^ d
      ≤ C ^ (n * n) * (1 + β) ^ (d * (n * n))
        * Real.exp ((d : ℝ) * ((r : ℝ) * ((n : ℝ) - r)) * t) := by
  intro n r d hr C β t hC hβ ht
  have hnn : ∀ (i j : Fin n), 0 ≤
      C * (1 + β * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1)) ^ d := by
    intro i j
    have : 0 ≤ (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1) := by
      split_ifs <;> positivity
    positivity
  have step : ∏ i : Fin n, ∏ j : Fin n,
        C * (1 + β * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1)) ^ d
      ≤ ∏ i : Fin n, ∏ j : Fin n, ((C * (1 + β) ^ d) *
          (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp ((d : ℝ) * t) else 1)) := by
    apply Finset.prod_le_prod
    · intro i _
      exact Finset.prod_nonneg (fun j _ => hnn i j)
    · intro i _
      apply Finset.prod_le_prod
      · intro j _
        exact hnn i j
      · intro j _
        exact factor_le d C β t _ hC hβ ht
  refine step.trans (le_of_eq ?_)
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [prod_indicator n r hr, ← Real.exp_nat_mul, ← pow_mul]
  have hp : (((1 + β) ^ d) ^ n) ^ n = (1 + β) ^ (d * (n * n)) := by
    rw [← pow_mul, ← pow_mul]
  have : (((r * (n - r) : ℕ) : ℝ)) * ((d : ℝ) * t) = (d : ℝ) * ((r : ℝ) * ((n : ℝ) - r)) * t := by
    rw [Nat.cast_mul, Nat.cast_sub hr]
    ring
  rw [this]
  rw [hp]

end GlobalTheory.CompanionTheory.EntrywiseCount
