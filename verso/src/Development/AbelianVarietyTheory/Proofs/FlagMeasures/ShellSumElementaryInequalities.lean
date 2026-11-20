import Mathlib

open Matrix Finset Real

namespace GlobalTheory

/- English proof (translation)
Establish `hb : (1 : ℝ) + i ≤ 2 ^ i`. Establish `h` using `one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 by norm_num) i`. Evaluate the numerical expressions using `at h`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `he : Real.exp (-1) ≤ 1 / 2`.

Establish `h` using `Real.add_one_le_exp (1 : ℝ)`. Rewrite using `[Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) two_pos]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hi : (0 : ℝ) ≤ i` using `Nat.cast_nonneg i`. Establish `hexp : -T * 2 ^ i ≤ -T + (i : ℝ) * (-1)`.

Use polynomial arithmetic with `[mul_nonneg (show (0 : ℝ) ≤ T by linarith) (sub_nonneg.mpr hb), mul_nonneg (sub_nonneg.mpr hT) hi]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exp_neg_mul_two_pow_le_geometric (T : ℝ) (hT : 1 ≤ T) (i : ℕ) :
    Real.exp (-T * 2 ^ i) ≤ Real.exp (-T) * (1 / 2 : ℝ) ^ i := by
  have hb : (1 : ℝ) + i ≤ 2 ^ i := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 by norm_num) i
    norm_num at h
    linarith
  have he : Real.exp (-1) ≤ 1 / 2 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) two_pos]
    linarith
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hexp : -T * 2 ^ i ≤ -T + (i : ℝ) * (-1) := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ T by linarith) (sub_nonneg.mpr hb),
      mul_nonneg (sub_nonneg.mpr hT) hi]
  calc Real.exp (-T * 2 ^ i) ≤ Real.exp (-T + (i : ℝ) * (-1)) := Real.exp_le_exp.mpr hexp
    _ = Real.exp (-T) * Real.exp (-1) ^ i := by rw [Real.exp_add, Real.exp_nat_mul]
    _ ≤ Real.exp (-T) * (1 / 2 : ℝ) ^ i :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le he i) (Real.exp_pos _).le

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s ep c hep hs hc hc'`. Establish `hs0 : 0 ≤ s` using `le_trans hep.le hs`. Use `le_min ?_ ?_` and prove the remaining obligations. Rewrite using `[sq]`.

Conclude with `mul_le_mul_of_nonneg_right hs hs0`. Combine the equalities or inequalities in the displayed calculation. Introduce `T hT`. Establish `hg : Summable (fun i : ℕ => Real.exp (-T) * (1 / 2 : ℝ) ^ i)` using `summable_geometric_two.mul_left _`. Establish `hs : Summable (fun i : ℕ => Real.exp (-T * 2 ^ i))` using `Summable.of_nonneg_of_le (fun i => (Real.exp_pos _).le) (fun i => exp_neg_mul_two_pow_le_geometric T hT i) hg`.

Use `⟨hs, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Introduce `al be f h0 h2 hb0 hb1`. Proceed by induction on `f with`. Consider the case `zero => simp`.

Consider the case `succ n ih`. Establish `hX : 0 ≤ (al + be) ^ n - al ^ n` using `sub_nonneg.mpr (pow_le_pow_left₀ h0 (by linarith) n)`. Establish `ha : al ^ n ≤ 3 ^ n` using `pow_le_pow_left₀ h0 (by linarith) n`. Establish `h1 : (al + be) * ((al + be) ^ n - al ^ n) ≤ 3 * ((n : ℝ) * be * 3 ^ n)` using `mul_le_mul (by linarith) ih hX (by norm_num)`. Establish `h3 : be * al ^ n ≤ be * 3 ^ n` using `mul_le_mul_of_nonneg_left ha hb0`.

Establish `h4 : 0 ≤ be * 3 ^ n` using `mul_nonneg hb0 (pow_nonneg (by norm_num) n)`. Combine the equalities or inequalities in the displayed calculation. Use `push_cast`. Rewrite using `[pow_succ]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem shell_sum_elementary_inequalities :
    (∀ (s ep c : ℝ), 0 < ep → ep ≤ s → 0 < c → ep ≤ 1 / c → ep * s ≤ min (s ^ 2) (s / c)) ∧ (∀ T : ℝ, 1 ≤ T → Summable (fun i : ℕ => Real.exp (-T * 2 ^ i)) ∧ ∑' i : ℕ, Real.exp (-T * 2 ^ i) ≤ 2 * Real.exp (-T)) ∧ ∀ (al be : ℝ) (f : ℕ), 0 ≤ al → al ≤ 2 → 0 ≤ be → be ≤ 1 → (al + be) ^ f - al ^ f ≤ f * be * 3 ^ f := by
  refine ⟨?_, ?_, ?_⟩
  · intro s ep c hep hs hc hc'
    have hs0 : 0 ≤ s := le_trans hep.le hs
    refine le_min ?_ ?_
    · rw [sq]
      exact mul_le_mul_of_nonneg_right hs hs0
    · calc ep * s ≤ (1 / c) * s := mul_le_mul_of_nonneg_right hc' hs0
        _ = s / c := by ring
  · intro T hT
    have hg : Summable (fun i : ℕ => Real.exp (-T) * (1 / 2 : ℝ) ^ i) :=
      summable_geometric_two.mul_left _
    have hs : Summable (fun i : ℕ => Real.exp (-T * 2 ^ i)) :=
      Summable.of_nonneg_of_le (fun i => (Real.exp_pos _).le)
        (fun i => exp_neg_mul_two_pow_le_geometric T hT i) hg
    refine ⟨hs, ?_⟩
    calc ∑' i : ℕ, Real.exp (-T * 2 ^ i) ≤ ∑' i : ℕ, Real.exp (-T) * (1 / 2 : ℝ) ^ i :=
          Summable.tsum_le_tsum (fun i => exp_neg_mul_two_pow_le_geometric T hT i) hs hg
      _ = 2 * Real.exp (-T) := by rw [tsum_mul_left, tsum_geometric_two, mul_comm]
  · intro al be f h0 h2 hb0 hb1
    induction f with
    | zero => simp
    | succ n ih =>
      have hX : 0 ≤ (al + be) ^ n - al ^ n :=
        sub_nonneg.mpr (pow_le_pow_left₀ h0 (by linarith) n)
      have ha : al ^ n ≤ 3 ^ n := pow_le_pow_left₀ h0 (by linarith) n
      have h1 : (al + be) * ((al + be) ^ n - al ^ n) ≤ 3 * ((n : ℝ) * be * 3 ^ n) :=
        mul_le_mul (by linarith) ih hX (by norm_num)
      have h3 : be * al ^ n ≤ be * 3 ^ n := mul_le_mul_of_nonneg_left ha hb0
      have h4 : 0 ≤ be * 3 ^ n := mul_nonneg hb0 (pow_nonneg (by norm_num) n)
      calc (al + be) ^ (n + 1) - al ^ (n + 1)
          = (al + be) * ((al + be) ^ n - al ^ n) + be * al ^ n := by ring
        _ ≤ 3 * ((n : ℝ) * be * 3 ^ n) + be * 3 ^ n := by linarith
        _ ≤ ((n + 1 : ℕ) : ℝ) * be * 3 ^ (n + 1) := by
          push_cast
          rw [pow_succ]
          nlinarith

end GlobalTheory
