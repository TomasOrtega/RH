import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumPrimeLogDivPredLeLogAdd

namespace GlobalTheory.PrimeRecipSum
open Finset

/- English proof (translation)
Establish `hsub : (range (y + 1)).filter Nat.Prime ⊆ (range 9).filter Nat.Prime`. Introduce `p hp`. Simplify using `only [mem_filter, mem_range] at hp ⊢`. Conclude with `⟨by omega, hp.2⟩`. Establish `hnn : ∀ p ∈ (range 9).filter Nat.Prime, p ∉ (range (y + 1)).filter Nat.Prime → (0:ℝ) ≤ 1 / ((p : ℝ) - 1)`.

Introduce `p hp _`. Establish `h2 : (2:ℝ) ≤ p` using `by exact_mod_cast (mem_filter.1 hp).2.two_le`. Conclude with `div_nonneg (by norm_num) (by linarith)`. Use `(sum_le_sum_of_subset_of_nonneg hsub hnn).trans ?_` and prove the remaining obligations. Establish `e : (range 9).filter Nat.Prime = {2, 3, 5, 7}` using `by decide`.

Rewrite using `[e]`. Evaluate the numerical expressions.
-/
theorem sum_inv_pred_small (y : ℕ) (hy : y ≤ 8) :
    ∑ p ∈ (range (y + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1) ≤ 23 / 12 := by
  have hsub : (range (y + 1)).filter Nat.Prime ⊆ (range 9).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hnn : ∀ p ∈ (range 9).filter Nat.Prime, p ∉ (range (y + 1)).filter Nat.Prime →
      (0:ℝ) ≤ 1 / ((p : ℝ) - 1) := by
    intro p hp _
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2.two_le
    exact div_nonneg (by norm_num) (by linarith)
  refine (sum_le_sum_of_subset_of_nonneg hsub hnn).trans ?_
  have e : (range 9).filter Nat.Prime = {2, 3, 5, 7} := by decide
  rw [e]
  norm_num

/- English proof (translation)
Establish `hp2 : (2:ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Establish `ha : (0:ℝ) < (p:ℝ) - 1` using `by linarith`. Establish `hl : 0 < Real.log (y:ℝ)` using `Real.log_pos (by exact_mod_cast (by omega : 1 < y))`. Establish `hyp : y ≤ p ^ 2`. Use `Nat.mul_le_mul (show s + 1 ≤ p from hps) (show s + 1 ≤ p from hps)` as an intermediate fact.

Rewrite using `[sq]`. Use linear arithmetic over natural numbers and integers. Establish `hy' : (y:ℝ) ≤ (p:ℝ) ^ 2` using `by exact_mod_cast hyp`. Establish `hL : Real.log y ≤ 2 * Real.log p`. Use `Real.log_le_log (by positivity) hy'` as an intermediate fact.

Rewrite `this` using `[Real.log_pow]`. Move the coercions through the operations in `at this`. Conclude with `this`. Rewrite using `[div_mul_div_comm, div_le_div_iff₀ ha (by positivity)]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hL ha.le]`.
-/
theorem inv_pred_le_of_sqrt_lt (y s p : ℕ) (hy : 2 ≤ y) (hs : y < (s + 1) * (s + 1))
    (hp : Nat.Prime p) (hps : s < p) :
    1 / ((p : ℝ) - 1) ≤ 2 / Real.log y * (Real.log p / ((p : ℝ) - 1)) := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have ha : (0:ℝ) < (p:ℝ) - 1 := by linarith
  have hl : 0 < Real.log (y:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hyp : y ≤ p ^ 2 := by
    have := Nat.mul_le_mul (show s + 1 ≤ p from hps) (show s + 1 ≤ p from hps)
    rw [sq]; omega
  have hy' : (y:ℝ) ≤ (p:ℝ) ^ 2 := by exact_mod_cast hyp
  have hL : Real.log y ≤ 2 * Real.log p := by
    have := Real.log_le_log (by positivity) hy'
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  rw [div_mul_div_comm, div_le_div_iff₀ ha (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hL ha.le]

/- English proof (translation)
Introduce `y`. Proceed by induction on `y using Nat.strong_induction_on with`. Consider the case `_ y ih`. Introduce `hy3`. Establish `hy3' : (3:ℝ) ≤ y` using `by exact_mod_cast hy3`.

Establish `hl1 : 1 ≤ Real.log (y:ℝ)`. Establish `he` using `Real.exp_one_lt_d9`. Use `Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ y)` as an intermediate fact. Rewrite `this` using `[Real.log_exp]`. Then use the resulting hypothesis. Establish `hll : 0 ≤ Real.log (Real.log y)` using `Real.log_nonneg hl1`.

Break down `le_or_gt y 8 with hy8 | hy8` into its components or cases. Use `sum_inv_pred_small y hy8` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `set s := Nat.sqrt y with hs_def`. Establish `hs3 : 3 ≤ s` using `by rw [hs_def, Nat.le_sqrt]; omega`.

Establish `hsy : s < y` using `Nat.sqrt_lt_self (by omega)`. Establish `hss : s * s ≤ y` using `Nat.sqrt_le y`. Establish `hys : y < (s + 1) * (s + 1)` using `Nat.lt_succ_sqrt y`. Establish `ih'` using `ih s hsy hs3`. Establish `hsplit : ∑ p ∈ (range (y + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1) = ∑ p ∈ (range (s + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1) + ∑ p ∈ ((range (y + 1)).filter Nat.Prime).filter (fun p => ¬ p ≤ s), 1 / ((p : ℝ) - 1)`.

Rewrite using `[← sum_filter_add_sum_filter_not ((range (y + 1)).filter Nat.Prime) (fun p => p ≤ s)]`. Use `congr 1`. Apply `sum_congr _ (fun _ _ => rfl)` to reduce the goal to its premises. Use extensionality with `p`. Simplify using `only [mem_filter, mem_range]`.

Conclude with `⟨fun ⟨⟨_, h2⟩, h3⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨by omega, h2⟩, by omega⟩⟩`. Establish `hl2 : 2 < Real.log (y:ℝ)`. Establish `he : Real.exp 2 < 9`. Use `Real.exp_one_lt_d9` as an intermediate fact. Establish `e2 : Real.exp 2 = Real.exp 1 * Real.exp 1` using `by rw [← Real.exp_add]; norm_num`.

Rewrite using `[e2]`. Use polynomial arithmetic with `[Real.exp_pos 1]`. Establish `h9 : (9:ℝ) ≤ y` using `by exact_mod_cast (by omega : 9 ≤ y)`. Use `Real.log_lt_log (Real.exp_pos 2) (by linarith : Real.exp 2 < y)` as an intermediate fact. Rewrite `this` using `[Real.log_exp]`. Then use the resulting hypothesis.

Establish `htail : ∑ p ∈ ((range (y + 1)).filter Nat.Prime).filter (fun p => ¬ p ≤ s), 1 / ((p : ℝ) - 1) ≤ 2 / Real.log y * (Real.log y + 2.2)`. Establish `hc : (0:ℝ) ≤ 2 / Real.log y` using `div_nonneg (by norm_num) (by linarith)`. Combine the equalities or inequalities in the displayed calculation. Apply `sum_le_sum` to reduce the goal to its premises. Introduce `p hp`.

Simplify using `only [mem_filter, mem_range] at hp`. Conclude with `inv_pred_le_of_sqrt_lt y s p (by omega) hys hp.1.2 (by omega)`. Use `_ = 2 / Real.log y * ∑ p ∈ ((range (y + 1)).filter Nat.Prime).filter (fun p => ¬ p ≤ s), Real.log p / ((p : ℝ) - 1) := by rw [mul_sum]`. Use `_ ≤ 2 / Real.log y * ∑ p ∈ (range (y + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) := by`. Apply `mul_le_mul_of_nonneg_left _ hc` to reduce the goal to its premises.

Apply `sum_le_sum_of_subset_of_nonneg (filter_subset _ _)` to reduce the goal to its premises. Introduce `p hp _`. Establish `h2 : (2:ℝ) ≤ p` using `by exact_mod_cast (mem_filter.1 hp).2.two_le`. Conclude with `div_nonneg (Real.log_natCast_nonneg p) (by linarith)`. Use `_ ≤ 2 / Real.log y * (Real.log y + 2.2) := mul_le_mul_of_nonneg_left (GlobalTheory.PrimeLogSum.sum_log_div_pred_le y) hc`.

Establish `hfrac : 2 / Real.log y * (Real.log y + 2.2) ≤ 4.2`. Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hslog : 0 < Real.log (s:ℝ)` using `Real.log_pos (by exact_mod_cast (by omega : 1 < s))`. Establish `hslog2 : 2 * Real.log (s:ℝ) ≤ Real.log y`.

Establish `h : ((s:ℝ)) ^ 2 ≤ y`. Establish `: s ^ 2 ≤ y` using `by rw [sq]; exact hss`. Conclude with `this` after adjusting the coercions. Establish `hs0 : (0:ℝ) < s` using `by exact_mod_cast (by omega : 0 < s)`. Use `Real.log_le_log (by positivity) h` as an intermediate fact.

Rewrite `this` using `[Real.log_pow]`. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `hlls : Real.log (Real.log s) ≤ Real.log (Real.log y) - Real.log 2`. Rewrite using `[← Real.log_div (by linarith) (by norm_num)]`.

Conclude with `Real.log_le_log hslog (by linarith)`. Establish `hlog2` using `Real.log_two_gt_d9`. Rewrite using `[hsplit]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_inv_pred_le : ∀ y : ℕ, 3 ≤ y →
    ∑ p ∈ (Finset.range (y + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1)
      ≤ 7 * Real.log (Real.log y) + 6 := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
  intro hy3
  have hy3' : (3:ℝ) ≤ y := by exact_mod_cast hy3
  have hl1 : 1 ≤ Real.log (y:ℝ) := by
    have he := Real.exp_one_lt_d9
    have := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ y)
    rwa [Real.log_exp] at this
  have hll : 0 ≤ Real.log (Real.log y) := Real.log_nonneg hl1
  rcases le_or_gt y 8 with hy8 | hy8
  · have := sum_inv_pred_small y hy8
    linarith
  set s := Nat.sqrt y with hs_def
  have hs3 : 3 ≤ s := by rw [hs_def, Nat.le_sqrt]; omega
  have hsy : s < y := Nat.sqrt_lt_self (by omega)
  have hss : s * s ≤ y := Nat.sqrt_le y
  have hys : y < (s + 1) * (s + 1) := Nat.lt_succ_sqrt y
  have ih' := ih s hsy hs3
  have hsplit : ∑ p ∈ (range (y + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1)
      = ∑ p ∈ (range (s + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1)
        + ∑ p ∈ ((range (y + 1)).filter Nat.Prime).filter (fun p => ¬ p ≤ s),
            1 / ((p : ℝ) - 1) := by
    rw [← sum_filter_add_sum_filter_not ((range (y + 1)).filter Nat.Prime) (fun p => p ≤ s)]
    congr 1
    apply sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [mem_filter, mem_range]
    exact ⟨fun ⟨⟨_, h2⟩, h3⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨by omega, h2⟩, by omega⟩⟩
  have hl2 : 2 < Real.log (y:ℝ) := by
    have he : Real.exp 2 < 9 := by
      have := Real.exp_one_lt_d9
      have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [e2]; nlinarith [Real.exp_pos 1]
    have h9 : (9:ℝ) ≤ y := by exact_mod_cast (by omega : 9 ≤ y)
    have := Real.log_lt_log (Real.exp_pos 2) (by linarith : Real.exp 2 < y)
    rwa [Real.log_exp] at this
  have htail : ∑ p ∈ ((range (y + 1)).filter Nat.Prime).filter (fun p => ¬ p ≤ s),
      1 / ((p : ℝ) - 1) ≤ 2 / Real.log y * (Real.log y + 2.2) := by
    have hc : (0:ℝ) ≤ 2 / Real.log y := div_nonneg (by norm_num) (by linarith)
    calc _ ≤ ∑ p ∈ ((range (y + 1)).filter Nat.Prime).filter (fun p => ¬ p ≤ s),
            2 / Real.log y * (Real.log p / ((p : ℝ) - 1)) := by
          apply sum_le_sum
          intro p hp
          simp only [mem_filter, mem_range] at hp
          exact inv_pred_le_of_sqrt_lt y s p (by omega) hys hp.1.2 (by omega)
      _ = 2 / Real.log y * ∑ p ∈ ((range (y + 1)).filter Nat.Prime).filter (fun p => ¬ p ≤ s),
            Real.log p / ((p : ℝ) - 1) := by rw [mul_sum]
      _ ≤ 2 / Real.log y * ∑ p ∈ (range (y + 1)).filter Nat.Prime,
            Real.log p / ((p : ℝ) - 1) := by
          apply mul_le_mul_of_nonneg_left _ hc
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro p hp _
          have h2 : (2:ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2.two_le
          exact div_nonneg (Real.log_natCast_nonneg p) (by linarith)
      _ ≤ 2 / Real.log y * (Real.log y + 2.2) :=
          mul_le_mul_of_nonneg_left (GlobalTheory.PrimeLogSum.sum_log_div_pred_le y) hc
  have hfrac : 2 / Real.log y * (Real.log y + 2.2) ≤ 4.2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    linarith
  have hslog : 0 < Real.log (s:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < s))
  have hslog2 : 2 * Real.log (s:ℝ) ≤ Real.log y := by
    have h : ((s:ℝ)) ^ 2 ≤ y := by
      have : s ^ 2 ≤ y := by rw [sq]; exact hss
      exact_mod_cast this
    have hs0 : (0:ℝ) < s := by exact_mod_cast (by omega : 0 < s)
    have := Real.log_le_log (by positivity) h
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hlls : Real.log (Real.log s) ≤ Real.log (Real.log y) - Real.log 2 := by
    rw [← Real.log_div (by linarith) (by norm_num)]
    exact Real.log_le_log hslog (by linarith)
  have hlog2 := Real.log_two_gt_d9
  rw [hsplit]
  linarith

end GlobalTheory.PrimeRecipSum
