import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PrimeLogarithmTail.SumLogBlock

namespace PI.TailWork

open Finset

/- English proof (translation)
Rewrite using `[Real.log_le_iff_le_exp (by norm_num)]`. Establish `h1` using `Real.exp_one_gt_d9`. Establish `h2` using `Real.add_one_le_exp (0.11 : ℝ)`. Establish `he : Real.exp 1.11 = Real.exp 1 * Real.exp 0.11`. Rewrite using `[← Real.exp_add]`.

Evaluate the numerical expressions. Rewrite using `[he]`. Use `mul_le_mul h1.le h2 (by norm_num) (Real.exp_pos 1).le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_three_le : Real.log 3 ≤ 1.11 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.add_one_le_exp (0.11 : ℝ)
  have he : Real.exp 1.11 = Real.exp 1 * Real.exp 0.11 := by
    rw [← Real.exp_add]; norm_num
  rw [he]
  have := mul_le_mul h1.le h2 (by norm_num) (Real.exp_pos 1).le
  linarith

/- English proof (translation)
Establish `h25 : Real.log 25 = 2 * Real.log 5`. Rewrite using `[show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; norm_num`. Establish `h24 : Real.log 24 = 3 * Real.log 2 + Real.log 3`. Rewrite using `[show (24 : ℝ) = 2 ^ 3 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]`. Evaluate the numerical expressions.

Establish `hq : Real.log 25 - Real.log 24 ≤ 25 / 24 - 1`. Rewrite using `[← Real.log_div (by norm_num) (by norm_num)]`. Conclude with `Real.log_le_sub_one_of_pos (by norm_num)`. Combine the linear relations using `[Real.log_two_lt_d9, log_three_le]`.
-/
theorem log_five_le : Real.log 5 ≤ 1.62 := by
  have h25 : Real.log 25 = 2 * Real.log 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h24 : Real.log 24 = 3 * Real.log 2 + Real.log 3 := by
    rw [show (24 : ℝ) = 2 ^ 3 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have hq : Real.log 25 - Real.log 24 ≤ 25 / 24 - 1 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    exact Real.log_le_sub_one_of_pos (by norm_num)
  linarith [Real.log_two_lt_d9, log_three_le]

/- English proof (translation)
Rewrite using `[← Finset.sum_filter_add_sum_filter_not Q (fun p => p ∈ ({2, 3, 5} : Finset ℕ))]`. Apply `add_le_add` to reduce the goal to its premises. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `p hp`. Rewrite `hp`, the goal using `[Finset.mem_filter]`.

Conclude with `⟨hp.2, (hQ p hp.1).2⟩`. Introduce `p _ _`. Conclude with `div_nonneg (Real.log_natCast_nonneg p) (by positivity)`. Establish `h` using `tail_odd 3 le_rfl (Q.filter (fun p => p ∉ ({2, 3, 5} : Finset ℕ))) (by`. Introduce `p hp`.

Rewrite `hp` using `[Finset.mem_filter]`. Take `⟨hpQ, hpT⟩` from `hp`. Establish `hpr` using `(hQ p hpQ).1`. Use `⟨hpr, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`.

Use `replace hlt : p < 2 * 3 + 1 := not_le.mp hlt`. Establish `h2` using `hpr.two_le`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpT`. Take `⟨n2, n3, n5⟩` from `hpT`. Use `interval_cases p`.

Apply the tactic sequence `all_goals first`. Consider the case `exact (n2 rfl).elim`. Consider the case `exact (n3 rfl).elim`. Consider the case `exact (n5 rfl).elim`. Consider the case `exact absurd hpr (by norm_num))`.

Evaluate the numerical expressions using `at h ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem small_split (a : ℕ) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime ∧ a < p) :
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ p ∈ ({2, 3, 5} : Finset ℕ).filter (fun p => a < p), Real.log (p : ℝ) / (p : ℝ) ^ 2
        + 2.04 / 7 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Q (fun p => p ∈ ({2, 3, 5} : Finset ℕ))]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨hp.2, (hQ p hp.1).2⟩
    · intro p _ _
      exact div_nonneg (Real.log_natCast_nonneg p) (by positivity)
  · have h := tail_odd 3 le_rfl
      (Q.filter (fun p => p ∉ ({2, 3, 5} : Finset ℕ))) (by
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpQ, hpT⟩ := hp
        have hpr := (hQ p hpQ).1
        refine ⟨hpr, ?_⟩
        by_contra hlt
        replace hlt : p < 2 * 3 + 1 := not_le.mp hlt
        have h2 := hpr.two_le
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpT
        obtain ⟨n2, n3, n5⟩ := hpT
        interval_cases p
        all_goals first
          | exact (n2 rfl).elim
          | exact (n3 rfl).elim
          | exact (n5 rfl).elim
          | exact absurd hpr (by norm_num))
    norm_num at h ⊢
    linarith

/- English proof (translation)
Establish `l2` using `Real.log_two_lt_d9`. Establish `l3` using `log_three_le`. Establish `l5` using `log_five_le`. Apply the tactic sequence `interval_cases a <;> norm_num [Finset.sum_filter, Finset.sum_insert] <;> linarith`.
-/
private theorem sum_small_primes_log_div_sq_add_le (a : ℕ) (ha : a < 5) :
    ∑ p ∈ ({2, 3, 5} : Finset ℕ).filter (fun p => a < p), Real.log (p : ℝ) / (p : ℝ) ^ 2
      + 2.04 / 7 ≤ 2.04 / ((a : ℝ) + 1) := by
  have l2 := Real.log_two_lt_d9
  have l3 := log_three_le
  have l5 := log_five_le
  interval_cases a <;> norm_num [Finset.sum_filter, Finset.sum_insert] <;> linarith

/- English proof (translation)
Take `⟨m, hm⟩ : ∃ m, ⌊X⌋₊ = m` from `⟨_, rfl⟩`. Establish `hXm : X < (m : ℝ) + 1` using `hm ▸ Nat.lt_floor_add_one X`. Establish `hmX : (m : ℝ) ≤ X` using `hm ▸ Nat.floor_le hX.le`. Establish `hlt : ∀ p ∈ Q, m < p` using `fun p hp => hm ▸ (Nat.floor_lt hX.le).2 (hQ p hp).2`. Break down `lt_or_ge X 5 with h5 | h5` into its components or cases.

Establish `hm5 : m < 5` using `by exact_mod_cast (lt_of_le_of_lt hmX h5)`. Establish `h1` using `small_split m Q (fun p hp => ⟨(hQ p hp).1, hlt p hp⟩)`. Establish `h2` using `sum_small_primes_log_div_sq_add_le m hm5`. Establish `hinv : 1 / ((m : ℝ) + 1) ≤ 1 / X` using `one_div_le_one_div_of_le hX hXm.le`. Establish `h3 : 2.04 / ((m : ℝ) + 1) ≤ 2.04 / X`.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm5 : 5 ≤ m`. Rewrite using `[← hm]; exact Nat.le_floor (by exact_mod_cast h5)`. Take `⟨k, hk⟩ : ∃ k, (m + 1) / 2 = k` from `⟨_, rfl⟩`.

Establish `hk3 : 3 ≤ k` using `by omega`. Establish `hQk : ∀ p ∈ Q, p.Prime ∧ 2 * k + 1 ≤ p`. Introduce `p hp`. Establish `hpr` using `(hQ p hp).1`. Establish `hmp` using `hlt p hp`.

Use `⟨hpr, ?_⟩` and prove the remaining obligations. Break down `hpr.eq_two_or_odd with h | h` into its components or cases. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Establish `h` using `tail_odd k hk3 Q hQk`.

Establish `hkX : X ≤ 2 * (k : ℝ) + 1`. Establish `hn : m + 1 ≤ 2 * k + 1` using `by omega`. Establish `: (m : ℝ) + 1 ≤ 2 * (k : ℝ) + 1` using `by exact_mod_cast hn`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hinv : 1 / (2 * (k : ℝ) + 1) ≤ 1 / X` using `one_div_le_one_div_of_le hX hkX`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_log_div_sq_le_div (X : ℝ) (hX : 0 < X) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime ∧ X < (p : ℝ)) :
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / X := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, ⌊X⌋₊ = m := ⟨_, rfl⟩
  have hXm : X < (m : ℝ) + 1 := hm ▸ Nat.lt_floor_add_one X
  have hmX : (m : ℝ) ≤ X := hm ▸ Nat.floor_le hX.le
  have hlt : ∀ p ∈ Q, m < p := fun p hp => hm ▸ (Nat.floor_lt hX.le).2 (hQ p hp).2
  rcases lt_or_ge X 5 with h5 | h5
  · have hm5 : m < 5 := by exact_mod_cast (lt_of_le_of_lt hmX h5)
    have h1 := small_split m Q (fun p hp => ⟨(hQ p hp).1, hlt p hp⟩)
    have h2 := sum_small_primes_log_div_sq_add_le m hm5
    have hinv : 1 / ((m : ℝ) + 1) ≤ 1 / X := one_div_le_one_div_of_le hX hXm.le
    have h3 : 2.04 / ((m : ℝ) + 1) ≤ 2.04 / X := by
      calc 2.04 / ((m : ℝ) + 1) = 2.04 * (1 / ((m : ℝ) + 1)) := by ring
        _ ≤ 2.04 * (1 / X) := mul_le_mul_of_nonneg_left hinv (by norm_num)
        _ = 2.04 / X := by ring
    linarith
  · have hm5 : 5 ≤ m := by
      rw [← hm]; exact Nat.le_floor (by exact_mod_cast h5)
    obtain ⟨k, hk⟩ : ∃ k, (m + 1) / 2 = k := ⟨_, rfl⟩
    have hk3 : 3 ≤ k := by omega
    have hQk : ∀ p ∈ Q, p.Prime ∧ 2 * k + 1 ≤ p := by
      intro p hp
      have hpr := (hQ p hp).1
      have hmp := hlt p hp
      refine ⟨hpr, ?_⟩
      rcases hpr.eq_two_or_odd with h | h
      · omega
      · omega
    have h := tail_odd k hk3 Q hQk
    have hkX : X ≤ 2 * (k : ℝ) + 1 := by
      have hn : m + 1 ≤ 2 * k + 1 := by omega
      have : (m : ℝ) + 1 ≤ 2 * (k : ℝ) + 1 := by exact_mod_cast hn
      linarith
    have hinv : 1 / (2 * (k : ℝ) + 1) ≤ 1 / X := one_div_le_one_div_of_le hX hkX
    calc ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / (2 * (k : ℝ) + 1) := h
      _ = 2.04 * (1 / (2 * (k : ℝ) + 1)) := by ring
      _ ≤ 2.04 * (1 / X) := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 2.04 / X := by ring

end PI.TailWork
