import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PrimeCountBoundOf

namespace PI.PC

open Real

/- English proof (translation)
Rewrite using `[← log_mul (by norm_num) (by norm_num), ← log_mul (by norm_num) (by norm_num)]`. Evaluate the numerical expressions.
-/
theorem log_thirty : log 30 = log 2 + log 3 + log 5 := by
  rw [← log_mul (by norm_num) (by norm_num), ← log_mul (by norm_num) (by norm_num)]
  norm_num

/- English proof (translation)
Rewrite using `[← log_mul (by norm_num) (by norm_num)]`. Evaluate the numerical expressions.
-/
theorem log_six : log 6 = log 2 + log 3 := by
  rw [← log_mul (by norm_num) (by norm_num)]
  norm_num

/- English proof (translation)
Establish `h2` using `log_two_gt_d9`. Establish `h2'` using `log_two_lt_d9`. Establish `h3` using `log_three_gt_d9`. Establish `h3'` using `log_three_lt_d9`. Establish `h5` using `log_five_gt_d9`.

Establish `h5'` using `log_five_lt_d9`. Unfold `ANum chA`. Rewrite using `[log_thirty]`. Apply the tactic sequence `constructor <;> norm_num at * <;> linarith`.
-/
theorem chebyshevConstantNumeric : ANum := by
  have h2 := log_two_gt_d9
  have h2' := log_two_lt_d9
  have h3 := log_three_gt_d9
  have h3' := log_three_lt_d9
  have h5 := log_five_gt_d9
  have h5' := log_five_lt_d9
  unfold ANum chA
  rw [log_thirty]
  constructor <;> norm_num at * <;> linarith

/- English proof (translation)
Use `decide +kernel`.
-/
theorem lcmUpto_le_three_pow : ∀ n < 30, Nat.lcmUpto n ≤ 3 ^ n := by
  decide +kernel

/- English proof (translation)
Establish `hn : ⌊x⌋₊ < 30` using `(Nat.floor_lt h0).2 (by exact_mod_cast hx)`. Rewrite using `[Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_log_lcmUpto]`. Establish `h1 : ((Nat.lcmUpto ⌊x⌋₊ : ℕ) : ℝ) ≤ (3 : ℝ) ^ ⌊x⌋₊`. Conclude with `lcmUpto_le_three_pow _ hn` after adjusting the coercions. Establish `h2 : log ((Nat.lcmUpto ⌊x⌋₊ : ℕ) : ℝ) ≤ log ((3 : ℝ) ^ ⌊x⌋₊)` using `log_le_log (by exact_mod_cast Nat.lcmUpto_pos _) h1`.

Rewrite `h2` using `[log_pow]`. Establish `h3` using `log_three_lt_d9`. Establish `h4 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x` using `Nat.floor_le h0`. Establish `h5 : (0 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Establish `h6 : ((⌊x⌋₊ : ℕ) : ℝ) * log 3 ≤ ((⌊x⌋₊ : ℕ) : ℝ) * 1.1056` using `mul_le_mul_of_nonneg_left (by norm_num at h3 ⊢; linarith) h5`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem psi_le_of_lt_thirty {x : ℝ} (h0 : 0 ≤ x) (hx : x < 30) : Chebyshev.psi x ≤ 1.1056 * x := by
  have hn : ⌊x⌋₊ < 30 := (Nat.floor_lt h0).2 (by exact_mod_cast hx)
  rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_log_lcmUpto]
  have h1 : ((Nat.lcmUpto ⌊x⌋₊ : ℕ) : ℝ) ≤ (3 : ℝ) ^ ⌊x⌋₊ := by
    exact_mod_cast lcmUpto_le_three_pow _ hn
  have h2 : log ((Nat.lcmUpto ⌊x⌋₊ : ℕ) : ℝ) ≤ log ((3 : ℝ) ^ ⌊x⌋₊) :=
    log_le_log (by exact_mod_cast Nat.lcmUpto_pos _) h1
  rw [log_pow] at h2
  have h3 := log_three_lt_d9
  have h4 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le h0
  have h5 : (0 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have h6 : ((⌊x⌋₊ : ℕ) : ℝ) * log 3 ≤ ((⌊x⌋₊ : ℕ) : ℝ) * 1.1056 :=
    mul_le_mul_of_nonneg_left (by norm_num at h3 ⊢; linarith) h5
  nlinarith

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `x h1 hx`. Use `psi_le_of_lt_thirty (by linarith) (by simpa using hx)` as an intermediate fact. Use `sq_nonneg (log x)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `succ k ih`. Introduce `x h1 hx`. Break down `lt_or_ge x 30 with h30 | h30` into its components or cases. Use `psi_le_of_lt_thirty (by linarith) h30` as an intermediate fact.

Use `sq_nonneg (log x)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx6 : x / 6 < 30 * 6 ^ k`. Rewrite using `[div_lt_iff₀ (by norm_num)]`. Combine the equalities or inequalities in the displayed calculation.

Establish `e1` using `ih (x / 6) (by linarith) hx6`. Establish `e2` using `(hS x (by linarith)).1`. Establish `e3` using `hD x h30`. Establish `e4 : chA * x ≤ 0.9213 * x` using `mul_le_mul_of_nonneg_right hA.2 (by linarith)`. Establish `hl : log (x / 6) = log x - log 6` using `log_div (by linarith) (by norm_num)`.

Rewrite `e1` using `[hl]`. Establish `hL : 0 ≤ log x` using `log_nonneg h1`. Establish `l6a : 1.7917 ≤ log 6`. Rewrite using `[log_six]`. Use `log_two_gt_d9` as an intermediate fact.

Use `log_three_gt_d9` as an intermediate fact. Evaluate the numerical expressions using `at *`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `l6b : log 6 ≤ 1.7918`. Rewrite using `[log_six]`.

Use `log_two_lt_d9` as an intermediate fact. Use `log_three_lt_d9` as an intermediate fact. Evaluate the numerical expressions using `at *`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `p1 : 0 ≤ (1.4 * log 6 - 2.5) * log x` using `mul_nonneg (by linarith) hL`.

Establish `p2 : (log 6) ^ 2 ≤ 1.7918 ^ 2` using `pow_le_pow_left₀ (by linarith) l6b 2`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem psiUpperBound_of_lt_thirty_mul_six_pow (hA : ANum) (hD : DUpper) (hS : Sandwich) (k : ℕ) :
    ∀ x : ℝ, 1 ≤ x → x < 30 * 6 ^ k → Chebyshev.psi x ≤ 1.1056 * x + 0.7 * (log x) ^ 2 := by
  induction k with
  | zero =>
    intro x h1 hx
    have := psi_le_of_lt_thirty (by linarith) (by simpa using hx)
    have := sq_nonneg (log x)
    linarith
  | succ k ih =>
    intro x h1 hx
    rcases lt_or_ge x 30 with h30 | h30
    · have := psi_le_of_lt_thirty (by linarith) h30
      have := sq_nonneg (log x)
      linarith
    · have hx6 : x / 6 < 30 * 6 ^ k := by
        rw [div_lt_iff₀ (by norm_num)]
        calc x < 30 * 6 ^ (k + 1) := hx
          _ = 30 * 6 ^ k * 6 := by ring
      have e1 := ih (x / 6) (by linarith) hx6
      have e2 := (hS x (by linarith)).1
      have e3 := hD x h30
      have e4 : chA * x ≤ 0.9213 * x := mul_le_mul_of_nonneg_right hA.2 (by linarith)
      have hl : log (x / 6) = log x - log 6 := log_div (by linarith) (by norm_num)
      rw [hl] at e1
      have hL : 0 ≤ log x := log_nonneg h1
      have l6a : 1.7917 ≤ log 6 := by
        rw [log_six]; have := log_two_gt_d9; have := log_three_gt_d9; norm_num at *; linarith
      have l6b : log 6 ≤ 1.7918 := by
        rw [log_six]; have := log_two_lt_d9; have := log_three_lt_d9; norm_num at *; linarith
      have p1 : 0 ≤ (1.4 * log 6 - 2.5) * log x := mul_nonneg (by linarith) hL
      have p2 : (log 6) ^ 2 ≤ 1.7918 ^ 2 := pow_le_pow_left₀ (by linarith) l6b 2
      nlinarith

/- English proof (translation)
Introduce `x h1`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 6)`. Use `psiUpperBound_of_lt_thirty_mul_six_pow hA hD hS k x h1 ?_` and prove the remaining obligations. Establish `: (0 : ℝ) < 6 ^ k` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem chUpper_of (hA : ANum) (hD : DUpper) (hS : Sandwich) : CHUpper := by
  intro x h1
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 6)
  refine psiUpperBound_of_lt_thirty_mul_six_pow hA hD hS k x h1 ?_
  have : (0 : ℝ) < 6 ^ k := by positivity
  linarith

end PI.PC
