import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.Conclusion1OfGainBoundAll

noncomputable section

open scoped BigOperators

namespace Formalism.MainNotions.AuxBlock8.Pf

/- English proof (translation)
Establish `h : Summable (fun e : ℕ => y * (1 / p) ^ e)` using `(summable_geometric_of_lt_one (by positivity) (by rw [div_lt_one (by linarith)]; linarith)).mul_left y`. Use `h.congr (fun e => ?_)` and prove the remaining obligations. Rewrite using `[one_div, inv_pow, div_eq_mul_inv]`.
-/
theorem summable_geo (p y : ℝ) (hp : 2 ≤ p) : Summable (fun e : ℕ => y / p ^ e) := by
  have h : Summable (fun e : ℕ => y * (1 / p) ^ e) :=
    (summable_geometric_of_lt_one (by positivity) (by rw [div_lt_one (by linarith)]; linarith)).mul_left y
  refine h.congr (fun e => ?_)
  rw [one_div, inv_pow, div_eq_mul_inv]

/- English proof (translation)
Use `Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) (summable_geo p y hp)` and prove the remaining obligations. Use `split_ifs`. Conclude with `h0 e`. Conclude with `le_rfl`. Use `split_ifs`.

Conclude with `h1 e`. Conclude with `le_trans (h0 e) (h1 e)`.
-/
theorem summable_if_of_le (p y : ℝ) (hp : 2 ≤ p) (f : ℕ → ℝ) (Q : ℕ → Prop) [DecidablePred Q]
    (h0 : ∀ e, 0 ≤ f e) (h1 : ∀ e, f e ≤ y / p ^ e) : Summable (fun e => if Q e then f e else 0) := by
  refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) (summable_geo p y hp)
  · split_ifs
    · exact h0 e
    · exact le_rfl
  · split_ifs
    · exact h1 e
    · exact le_trans (h0 e) (h1 e)

/- English proof (translation)
Establish `h` using `(summable_geo p |y| hp)`. Use `Summable.of_norm_bounded h (fun e => ?_)` and prove the remaining obligations. Establish `hpe : 0 < p ^ e` using `by positivity`. Use `split_ifs`. Rewrite using `[Real.norm_eq_abs, abs_div, abs_of_pos hpe]`.

Rewrite using `[norm_zero]`. Check the signs of the components of the expression.
-/
theorem summable_odd (p y : ℝ) (hp : 2 ≤ p) (Q : ℕ → Prop) [DecidablePred Q] :
    Summable (fun e : ℕ => if Q e then y / p ^ e else 0) := by
  have h := (summable_geo p |y| hp)
  refine Summable.of_norm_bounded h (fun e => ?_)
  have hpe : 0 < p ^ e := by positivity
  split_ifs
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hpe]
  · rw [norm_zero]; positivity

/- English proof (translation)
Use `set f : ℕ → ℝ := fun e => if Q e then y / p ^ e else 0 with hf`. Establish `he : ∀ k : ℕ, f (2 * k) = 0`. Introduce `k`. Rewrite using `[hf]`. Conclude with `if_neg (fun h => by have := (hQ _).1 h; exact (Nat.not_odd_iff_even.2 (even_two_mul k)) this)`.

Establish `ho : ∀ k : ℕ, f (2 * k + 1) = y / p * (1 / p ^ 2) ^ k`. Introduce `k`. Rewrite using `[hf]`. Establish `: Q (2 * k + 1)` using `(hQ _).2 (odd_two_mul_add_one k)`. Simplify using `only [if_pos this]`.

Rewrite using `[pow_succ, pow_mul, one_div, inv_pow]`. Clear the denominators using the available nonvanishing facts. Establish `hp2 : (1 : ℝ) / p ^ 2 < 1`. Rewrite using `[div_lt_one (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hs0 : Summable (fun k : ℕ => f (2 * k))`. Simplify using `only [he]`. Conclude with `summable_zero`. Establish `hs1 : Summable (fun k : ℕ => f (2 * k + 1))`. Simplify using `only [ho]`.

Conclude with `(summable_geometric_of_lt_one (by positivity) hp2).mul_left _`. Rewrite using `[← tsum_even_add_odd hs0 hs1]`. Simplify using `only [he, ho, tsum_zero, zero_add]`. Rewrite using `[tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hp2]`. Establish `h1 : p ^ 2 - 1 ≠ 0` using `by nlinarith`.

Establish `h2 : p ≠ 0` using `by linarith`. Establish `h3 : (1 : ℝ) - 1 / p ^ 2 ≠ 0` using `by linarith`. Clear the denominators using the available nonvanishing facts.
-/
theorem tsum_odd (p y : ℝ) (hp : 2 ≤ p) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ e, Q e ↔ Odd e) :
    ∑' e : ℕ, (if Q e then y / p ^ e else 0) = p / (p ^ 2 - 1) * y := by
  set f : ℕ → ℝ := fun e => if Q e then y / p ^ e else 0 with hf
  have he : ∀ k : ℕ, f (2 * k) = 0 := by
    intro k
    rw [hf]
    exact if_neg (fun h => by have := (hQ _).1 h; exact (Nat.not_odd_iff_even.2 (even_two_mul k)) this)
  have ho : ∀ k : ℕ, f (2 * k + 1) = y / p * (1 / p ^ 2) ^ k := by
    intro k
    rw [hf]
    have : Q (2 * k + 1) := (hQ _).2 (odd_two_mul_add_one k)
    simp only [if_pos this]
    rw [pow_succ, pow_mul, one_div, inv_pow]
    field_simp
  have hp2 : (1 : ℝ) / p ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  have hs0 : Summable (fun k : ℕ => f (2 * k)) := by
    simp only [he]; exact summable_zero
  have hs1 : Summable (fun k : ℕ => f (2 * k + 1)) := by
    simp only [ho]
    exact (summable_geometric_of_lt_one (by positivity) hp2).mul_left _
  rw [← tsum_even_add_odd hs0 hs1]
  simp only [he, ho, tsum_zero, zero_add]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hp2]
  have h1 : p ^ 2 - 1 ≠ 0 := by nlinarith
  have h2 : p ≠ 0 := by linarith
  have h3 : (1 : ℝ) - 1 / p ^ 2 ≠ 0 := by linarith
  field_simp

/- English proof (translation)
Break down `le_total u w with h | h` into its components or cases. Rewrite using `[max_eq_left (by linarith), min_eq_left h]; ring`. Rewrite using `[max_eq_right (by linarith), min_eq_right h]; ring`.
-/
theorem max_add_min_eq (u w : ℝ) : max 0 (u - w) + min u w = u := by
  rcases le_total u w with h | h
  · rw [max_eq_left (by linarith), min_eq_left h]; ring
  · rw [max_eq_right (by linarith), min_eq_right h]; ring

/- English proof (translation)
Establish `hpe : ∀ e : ℕ, 0 ≤ y / p ^ e` using `fun e => div_nonneg hy (by positivity)`. Establish `s1 : Summable (fun e : ℕ => if Q e then max 0 (y / p ^ e - w e) else 0)` using `summable_if_of_le p y hp _ Q (fun e => le_max_left _ _) (fun e => max_le (hpe e) (by have := hw e; linarith))`. Establish `s2 : Summable (fun e : ℕ => if Q e then min (y / p ^ e) (w e) else 0)` using `summable_if_of_le p y hp _ Q (fun e => le_min (hpe e) (hw e)) (fun e => min_le_left _ _)`. Rewrite using `[← s1.tsum_add s2, ← tsum_odd p y hp Q hQ]`. Use `congr 1`.

Use function extensionality and compare the values at `e`. Use `split_ifs`. Conclude with `max_add_min_eq _ _`. Simplify using the standard rewrite rules.
-/
theorem tsum_pos_add_min (p y : ℝ) (hp : 2 ≤ p) (hy : 0 ≤ y) (w : ℕ → ℝ) (hw : ∀ e, 0 ≤ w e)
    (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ e, Q e ↔ Odd e) :
    ∑' e : ℕ, (if Q e then max 0 (y / p ^ e - w e) else 0) +
      ∑' e : ℕ, (if Q e then min (y / p ^ e) (w e) else 0) = p / (p ^ 2 - 1) * y := by
  have hpe : ∀ e : ℕ, 0 ≤ y / p ^ e := fun e => div_nonneg hy (by positivity)
  have s1 : Summable (fun e : ℕ => if Q e then max 0 (y / p ^ e - w e) else 0) :=
    summable_if_of_le p y hp _ Q (fun e => le_max_left _ _)
      (fun e => max_le (hpe e) (by have := hw e; linarith))
  have s2 : Summable (fun e : ℕ => if Q e then min (y / p ^ e) (w e) else 0) :=
    summable_if_of_le p y hp _ Q (fun e => le_min (hpe e) (hw e)) (fun e => min_le_left _ _)
  rw [← s1.tsum_add s2, ← tsum_odd p y hp Q hQ]
  congr 1
  funext e
  split_ifs
  · exact max_add_min_eq _ _
  · simp

/- English proof (translation)
Establish `hpe : ∀ e : ℕ, 0 ≤ y / p ^ e` using `fun e => div_nonneg hy (by positivity)`. Rewrite using `[← tsum_odd p y hp (fun e => Odd e) (fun e => Iff.rfl)]`. Use `Summable.tsum_le_tsum (fun e => ?_) (summable_if_of_le p y hp _ Q (fun e => le_max_left _ _) (fun e => max_le (hpe e) (by have := hw e; linarith))) (summable_odd p y hp _)` and prove the remaining obligations. Distinguish the cases in `h : Q e`. Rewrite using `[if_pos h, if_pos (hQ e h)]`.

Conclude with `max_le (hpe e) (by have := hw e; linarith)`. Rewrite using `[if_neg h] split_ifs`. Conclude with `hpe e`. Conclude with `le_rfl`.
-/
theorem tsum_pos_le (p y : ℝ) (hp : 2 ≤ p) (hy : 0 ≤ y) (w : ℕ → ℝ) (hw : ∀ e, 0 ≤ w e)
    (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ e, Q e → Odd e) :
    ∑' e : ℕ, (if Q e then max 0 (y / p ^ e - w e) else 0) ≤ p / (p ^ 2 - 1) * y := by
  classical
  have hpe : ∀ e : ℕ, 0 ≤ y / p ^ e := fun e => div_nonneg hy (by positivity)
  rw [← tsum_odd p y hp (fun e => Odd e) (fun e => Iff.rfl)]
  refine Summable.tsum_le_tsum (fun e => ?_)
    (summable_if_of_le p y hp _ Q (fun e => le_max_left _ _)
      (fun e => max_le (hpe e) (by have := hw e; linarith))) (summable_odd p y hp _)
  by_cases h : Q e
  · rw [if_pos h, if_pos (hQ e h)]
    exact max_le (hpe e) (by have := hw e; linarith)
  · rw [if_neg h]
    split_ifs
    · exact hpe e
    · exact le_rfl

/- English proof (translation)
Establish `hy0 : 0 ≤ y` using `by linarith`. Use `set M : ℕ := ⌊Real.logb p A⌋₊ with hM`. Establish `hlog : 0 ≤ Real.logb p A` using `Real.logb_nonneg (by linarith) hA`. Establish `hpe : ∀ e : ℕ, 0 ≤ y / p ^ e` using `fun e => div_nonneg hy0 (by positivity)`. Establish `hpe' : ∀ e : ℕ, 0 ≤ (y - 2 * c) / p ^ e` using `fun e => div_nonneg (by linarith) (by positivity)`.

Establish `sF : Summable (fun e : ℕ => if Q e then max 0 (y / p ^ e - w e) else 0)` using `summable_if_of_le p y hp _ Q (fun e => le_max_left _ _) (fun e => max_le (hpe e) (by have := hw e; linarith))`. Establish `sG : Summable (fun e : ℕ => if Q e then max 0 ((y - 2 * c) / p ^ e - w' e) else 0)` using `summable_if_of_le p (y - 2 * c) hp _ Q (fun e => le_max_left _ _) (fun e => max_le (hpe' e) (by have := hw0 e; linarith))`. Establish `sH : Summable (fun e : ℕ => if e ∈ Finset.Icc 1 M then 3 * c else 0)` using `summable_of_ne_finset_zero (s := Finset.Icc 1 M) (fun e he => if_neg he)`. Establish `hH : ∑' e : ℕ, (if e ∈ Finset.Icc 1 M then 3 * c else 0) ≤ 3 * c * Real.logb p A`. Rewrite using `[tsum_eq_sum (s := Finset.Icc 1 M) (fun e he => if_neg he)]`.

Rewrite using `[Finset.sum_congr rfl (fun e he => if_pos he), Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]`. Establish `h1 : ((M + 1 - 1 : ℕ) : ℝ) ≤ Real.logb p A`. Rewrite using `[Nat.add_sub_cancel]`. Conclude with `Nat.floor_le hlog`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hterm : ∀ e : ℕ, (if Q e then max 0 (y / p ^ e - w e) else 0) ≤ (if Q e then max 0 ((y - 2 * c) / p ^ e - w' e) else 0) + (if e ∈ Finset.Icc 1 M then 3 * c else 0)`. Introduce `e`. Establish `h3c : (0 : ℝ) ≤ (if e ∈ Finset.Icc 1 M then 3 * c else 0)` using `by split_ifs`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_rfl`.

Distinguish the cases in `h : Q e`. Rewrite using `[if_pos h, if_pos h]`. Distinguish the cases in `hpos : y / p ^ e ≤ w e`. Rewrite using `[max_eq_left (by linarith)]`. Conclude with `add_nonneg (le_max_left _ _) h3c`.

Use `push_neg at hpos`. Establish `hpp : (0 : ℝ) < p ^ e` using `by positivity`. Establish `h1 : 1 < y / p ^ e` using `lt_of_le_of_lt (hw e) hpos`. Establish `h2 : p ^ e < y` using `by rwa [lt_div_iff₀ hpp, one_mul] at h1`. Establish `h3 : (e : ℝ) ≤ Real.logb p A`.

Rewrite using `[Real.le_logb_iff_rpow_le (by linarith) (by linarith), Real.rpow_natCast]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : e ∈ Finset.Icc 1 M`. Rewrite using `[Finset.mem_Icc]`. Use `⟨?_, Nat.le_floor h3⟩` and prove the remaining obligations.

Take `⟨k, hk⟩` from `hQ e h`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_pos h4, max_eq_right (by linarith)]`. Establish `h5 : 2 * c / p ^ e ≤ 2 * c` using `div_le_self (by linarith) (one_le_pow₀ (by linarith))`. Establish `h6 : (y - 2 * c) / p ^ e = y / p ^ e - 2 * c / p ^ e` using `sub_div _ _ _`.

Establish `h7` using `hw' e`. Establish `h8 : (y - 2 * c) / p ^ e - w' e ≤ max 0 ((y - 2 * c) / p ^ e - w' e)` using `le_max_right _ _`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[if_neg h, if_neg h]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `Summable.tsum_le_tsum hterm sF (sG.add sH)` as an intermediate fact. Rewrite `this` using `[sG.tsum_add sH]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tsum_truncated_shift_le (p y c A : ℝ) (hp : 2 ≤ p) (hc : 0 ≤ c) (hy : 2 * c ≤ y) (hyA : y ≤ A) (hA : 1 ≤ A)
    (w w' : ℕ → ℝ) (hw : ∀ e, 1 ≤ w e) (hw0 : ∀ e, 0 ≤ w' e) (hw' : ∀ e, w' e ≤ w e + c)
    (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ e, Q e → Odd e) :
    ∑' e : ℕ, (if Q e then max 0 (y / p ^ e - w e) else 0) - 3 * c * Real.logb p A ≤
      ∑' e : ℕ, (if Q e then max 0 ((y - 2 * c) / p ^ e - w' e) else 0) := by
  classical
  have hy0 : 0 ≤ y := by linarith
  set M : ℕ := ⌊Real.logb p A⌋₊ with hM
  have hlog : 0 ≤ Real.logb p A := Real.logb_nonneg (by linarith) hA
  have hpe : ∀ e : ℕ, 0 ≤ y / p ^ e := fun e => div_nonneg hy0 (by positivity)
  have hpe' : ∀ e : ℕ, 0 ≤ (y - 2 * c) / p ^ e := fun e => div_nonneg (by linarith) (by positivity)
  have sF : Summable (fun e : ℕ => if Q e then max 0 (y / p ^ e - w e) else 0) :=
    summable_if_of_le p y hp _ Q (fun e => le_max_left _ _)
      (fun e => max_le (hpe e) (by have := hw e; linarith))
  have sG : Summable (fun e : ℕ => if Q e then max 0 ((y - 2 * c) / p ^ e - w' e) else 0) :=
    summable_if_of_le p (y - 2 * c) hp _ Q (fun e => le_max_left _ _)
      (fun e => max_le (hpe' e) (by have := hw0 e; linarith))
  have sH : Summable (fun e : ℕ => if e ∈ Finset.Icc 1 M then 3 * c else 0) :=
    summable_of_ne_finset_zero (s := Finset.Icc 1 M) (fun e he => if_neg he)
  have hH : ∑' e : ℕ, (if e ∈ Finset.Icc 1 M then 3 * c else 0) ≤ 3 * c * Real.logb p A := by
    rw [tsum_eq_sum (s := Finset.Icc 1 M) (fun e he => if_neg he)]
    rw [Finset.sum_congr rfl (fun e he => if_pos he), Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have h1 : ((M + 1 - 1 : ℕ) : ℝ) ≤ Real.logb p A := by
      rw [Nat.add_sub_cancel]
      exact Nat.floor_le hlog
    nlinarith
  have hterm : ∀ e : ℕ, (if Q e then max 0 (y / p ^ e - w e) else 0) ≤
      (if Q e then max 0 ((y - 2 * c) / p ^ e - w' e) else 0) +
        (if e ∈ Finset.Icc 1 M then 3 * c else 0) := by
    intro e
    have h3c : (0 : ℝ) ≤ (if e ∈ Finset.Icc 1 M then 3 * c else 0) := by
      split_ifs
      · linarith
      · exact le_rfl
    by_cases h : Q e
    · rw [if_pos h, if_pos h]
      by_cases hpos : y / p ^ e ≤ w e
      · rw [max_eq_left (by linarith)]
        exact add_nonneg (le_max_left _ _) h3c
      · push_neg at hpos
        have hpp : (0 : ℝ) < p ^ e := by positivity
        have h1 : 1 < y / p ^ e := lt_of_le_of_lt (hw e) hpos
        have h2 : p ^ e < y := by rwa [lt_div_iff₀ hpp, one_mul] at h1
        have h3 : (e : ℝ) ≤ Real.logb p A := by
          rw [Real.le_logb_iff_rpow_le (by linarith) (by linarith), Real.rpow_natCast]
          linarith
        have h4 : e ∈ Finset.Icc 1 M := by
          rw [Finset.mem_Icc]
          refine ⟨?_, Nat.le_floor h3⟩
          obtain ⟨k, hk⟩ := hQ e h
          omega
        rw [if_pos h4, max_eq_right (by linarith)]
        have h5 : 2 * c / p ^ e ≤ 2 * c := div_le_self (by linarith) (one_le_pow₀ (by linarith))
        have h6 : (y - 2 * c) / p ^ e = y / p ^ e - 2 * c / p ^ e := sub_div _ _ _
        have h7 := hw' e
        have h8 : (y - 2 * c) / p ^ e - w' e ≤ max 0 ((y - 2 * c) / p ^ e - w' e) := le_max_right _ _
        linarith
    · rw [if_neg h, if_neg h]
      linarith
  have := Summable.tsum_le_tsum hterm sF (sG.add sH)
  rw [sG.tsum_add sH] at this
  linarith

end Formalism.MainNotions.AuxBlock8.Pf

end
