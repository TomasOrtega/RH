import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.Small

/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Establish `hL : Real.log (x + 1) - Real.log x ≤ 1 / x`. Rewrite using `[← Real.log_div (by positivity) (by positivity)]`. Establish `h` using `Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)`. Establish `he : (x + 1) / x - 1 = 1 / x`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hK : (x + 1) * (Real.log (x + 1) - Real.log x) ≤ 2`. Establish `h1 : (x + 1) * (Real.log (x + 1) - Real.log x) ≤ (x + 1) * (1 / x)` using `mul_le_mul_of_nonneg_left hL (by linarith)`.

Establish `h2 : (x + 1) * (1 / x) ≤ 2`. Rewrite using `[mul_one_div, div_le_iff₀ hx0]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hE : (Real.log x + 2) / x - (Real.log (x + 1) + 2) / (x + 1) - Real.log (x + 1) / ((x + 1) * x) = (2 - (x + 1) * (Real.log (x + 1) - Real.log x)) / ((x + 1) * x)`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : 0 ≤ (2 - (x + 1) * (Real.log (x + 1) - Real.log x)) / ((x + 1) * x)` using `div_nonneg (by linarith) (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_tail_step (x : ℝ) (hx : 1 ≤ x) :
    Real.log (x + 1) / ((x + 1) * x) ≤
      (Real.log x + 2) / x - (Real.log (x + 1) + 2) / (x + 1) := by
  have hx0 : 0 < x := by linarith
  have hL : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    have he : (x + 1) / x - 1 = 1 / x := by
      field_simp
      ring
    linarith
  have hK : (x + 1) * (Real.log (x + 1) - Real.log x) ≤ 2 := by
    have h1 : (x + 1) * (Real.log (x + 1) - Real.log x) ≤ (x + 1) * (1 / x) :=
      mul_le_mul_of_nonneg_left hL (by linarith)
    have h2 : (x + 1) * (1 / x) ≤ 2 := by
      rw [mul_one_div, div_le_iff₀ hx0]
      linarith
    linarith
  have hE : (Real.log x + 2) / x - (Real.log (x + 1) + 2) / (x + 1) - Real.log (x + 1) / ((x + 1) * x) =
      (2 - (x + 1) * (Real.log (x + 1) - Real.log x)) / ((x + 1) * x) := by
    field_simp
    ring
  have hpos : 0 ≤ (2 - (x + 1) * (Real.log (x + 1) - Real.log x)) / ((x + 1) * x) :=
    div_nonneg (by linarith) (by positivity)
  linarith

/- English proof (translation)
Proceed by induction on `N, hN using Nat.le_induction with`. Consider the case `base`. Rewrite using `[Finset.Icc_eq_empty (by norm_num)]`. Simplify using the standard rewrite rules. Consider the case `succ k hk ih`.

Rewrite using `[Finset.sum_Icc_succ_top (by omega)]`. Establish `hstep` using `log_tail_step (k : ℝ) (by exact_mod_cast hk)`. Establish `hc : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1` using `by push_cast; ring`. Rewrite using `[hc]`. Establish `hc2 : (k : ℝ) + 1 - 1 = k` using `by ring`.

Rewrite using `[hc2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_tail_Icc (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 2 N, Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) ≤
      2 - (Real.log N + 2) / N := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty (by norm_num)]
    simp
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hstep := log_tail_step (k : ℝ) (by exact_mod_cast hk)
    have hc : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hc]
    have hc2 : (k : ℝ) + 1 - 1 = k := by ring
    rw [hc2]
    linarith

/- English proof (translation)
Introduce `S hS`. Establish `hN : 1 ≤ max 1 (S.sup id)` using `le_max_left _ _`. Establish `hsub : S ⊆ Finset.Icc 2 (max 1 (S.sup id))`. Introduce `n hn`. Rewrite using `[Finset.mem_Icc]`.

Conclude with `⟨hS n hn, le_trans (Finset.le_sup (f := id) hn) (le_max_right _ _)⟩`. Establish `hnn : ∀ n ∈ Finset.Icc 2 (max 1 (S.sup id)), 0 ≤ Real.log n / ((n : ℝ) * ((n : ℝ) - 1))`. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_Icc]`. Establish `h2 : (2 : ℝ) ≤ n` using `by exact_mod_cast hn.1`.

Apply `div_nonneg (Real.log_nonneg (by linarith))` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `h1 : (1 : ℝ) ≤ ((max 1 (S.sup id) : ℕ) : ℝ)` using `by exact_mod_cast hN`. Establish `hq : 0 ≤ (Real.log ((max 1 (S.sup id) : ℕ) : ℝ) + 2) / ((max 1 (S.sup id) : ℕ) : ℝ)` using `div_nonneg (by linarith [Real.log_nonneg h1]) (by linarith)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem log_tail :
    ∀ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n) →
      ∑ n ∈ S, Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 2 := by
  intro S hS
  have hN : 1 ≤ max 1 (S.sup id) := le_max_left _ _
  have hsub : S ⊆ Finset.Icc 2 (max 1 (S.sup id)) := by
    intro n hn
    rw [Finset.mem_Icc]
    exact ⟨hS n hn, le_trans (Finset.le_sup (f := id) hn) (le_max_right _ _)⟩
  have hnn : ∀ n ∈ Finset.Icc 2 (max 1 (S.sup id)), 0 ≤ Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith
  have h1 : (1 : ℝ) ≤ ((max 1 (S.sup id) : ℕ) : ℝ) := by exact_mod_cast hN
  have hq : 0 ≤ (Real.log ((max 1 (S.sup id) : ℕ) : ℝ) + 2) / ((max 1 (S.sup id) : ℕ) : ℝ) :=
    div_nonneg (by linarith [Real.log_nonneg h1]) (by linarith)
  calc ∑ n ∈ S, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
      ≤ ∑ n ∈ Finset.Icc 2 (max 1 (S.sup id)), Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => hnn n hn)
    _ ≤ 2 - (Real.log ((max 1 (S.sup id) : ℕ) : ℝ) + 2) / ((max 1 (S.sup id) : ℕ) : ℝ) :=
        log_tail_Icc _ hN
    _ ≤ 2 := by linarith

end GlobalTheory.CompanionTheory.Ar.Small
