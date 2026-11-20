import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PrimeCountBoundOf

noncomputable section

namespace PI.PC

open Finset Real
open scoped Nat

/- English proof (translation)
Establish `hb : 0 < b` using `lt_of_lt_of_le ha hab`. Establish `h` using `Real.one_sub_inv_le_log_of_pos (div_pos hb ha)`. Rewrite `h` using `[Real.log_div hb.ne' ha.ne', inv_div]`. Establish `h2 : b - a ≤ b * (log b - log a)`. Establish `h3` using `mul_le_mul_of_nonneg_left h hb.le`.

Rewrite `h3` using `[mul_sub, mul_one, mul_div_cancel₀ _ hb.ne']`. Then use the resulting hypothesis. Establish `e : (b * log b - b) - (a * log a - a) - (b - a) * log a = b * (log b - log a) - (b - a)`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem g_diff {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * log a ≤ (b * log b - b) - (a * log a - a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne', inv_div] at h
  have h2 : b - a ≤ b * (log b - log a) := by
    have h3 := mul_le_mul_of_nonneg_left h hb.le
    rwa [mul_sub, mul_one, mul_div_cancel₀ _ hb.ne'] at h3
  have e : (b * log b - b) - (a * log a - a) - (b - a) * log a = b * (log b - log a) - (b - a) := by
    ring
  linarith

/- English proof (translation)
Establish `h` using `g_diff (by linarith : (0 : ℝ) < a) hab`. Establish `hl : 0 ≤ (b - a) * log a` using `mul_nonneg (by linarith) (Real.log_nonneg ha)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem g_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : a * log a - a ≤ b * log b - b := by
  have h := g_diff (by linarith : (0 : ℝ) < a) hab
  have hl : 0 ≤ (b - a) * log a := mul_nonneg (by linarith) (Real.log_nonneg ha)
  linarith

/- English proof (translation)
Establish `h` using `Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem third_le_log : (1 : ℝ) / 3 ≤ log (3 / 2) := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  calc (1 : ℝ) / 3 = 1 - (3 / 2)⁻¹ := by norm_num
    _ ≤ log (3 / 2) := h

/- English proof (translation)
Establish `ha0 : (0 : ℝ) < a` using `by linarith`. Establish `hb0 : (0 : ℝ) < b` using `by linarith`. Establish `hg` using `g_diff ha0 hab`. Establish `hlog : log b - log a ≤ (b - a) / a`. Establish `h` using `Real.log_le_sub_one_of_pos (div_pos hb0 ha0)`.

Rewrite `h` using `[Real.log_div hb0.ne' ha0.ne']`. Rewrite `h` using `[show b / a - 1 = (b - a) / a by field_simp]`. Then use the resulting hypothesis. Establish `hla : 1 / 3 ≤ log a` using `le_trans third_le_log (Real.log_le_log (by norm_num) ha)`. Establish `h3 : (b - a) / a ≤ (b - a) * (2 / 3)`. Rewrite using `[div_le_iff₀ ha0]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h4 : (b - a) * (1 / 3) ≤ (b - a) * log a` using `mul_le_mul_of_nonneg_left hla (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem h_mono {a b : ℝ} (ha : 3 / 2 ≤ a) (hab : a ≤ b) :
    a * log a - a - log a / 2 ≤ b * log b - b - log b / 2 := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hg := g_diff ha0 hab
  have hlog : log b - log a ≤ (b - a) / a := by
    have h := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    rw [Real.log_div hb0.ne' ha0.ne'] at h
    rwa [show b / a - 1 = (b - a) / a by field_simp] at h
  have hla : 1 / 3 ≤ log a := le_trans third_le_log (Real.log_le_log (by norm_num) ha)
  have h3 : (b - a) / a ≤ (b - a) * (2 / 3) := by
    rw [div_le_iff₀ ha0]
    nlinarith
  have h4 : (b - a) * (1 / 3) ≤ (b - a) * log a := mul_le_mul_of_nonneg_left hla (by linarith)
  linarith

/- English proof (translation)
Distinguish the cases in `ha' : 3 / 2 ≤ a`. Conclude with `h_mono ha' hab`. Use `push_neg at ha'`. Establish `hb2` using `h_mono (a := 2) (b := b) (by norm_num) hb`. Establish `hla : log a ≤ a - 1` using `Real.log_le_sub_one_of_pos (by linarith)`.

Establish `hq : (a - 1 / 2) * log a ≤ (a - 1 / 2) * (a - 1)` using `mul_le_mul_of_nonneg_left hla (by linarith)`. Establish `hq2 : (a - 1 / 2) * (a - 1) - a ≤ -1` using `by nlinarith`. Establish `h2 : -1 ≤ 2 * log 2 - 2 - log 2 / 2`. Use `Real.log_two_gt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e : (a - 1 / 2) * log a = a * log a - log a / 2` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem h_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : 2 ≤ b) :
    a * log a - a - log a / 2 ≤ b * log b - b - log b / 2 := by
  by_cases ha' : 3 / 2 ≤ a
  · exact h_mono ha' hab
  push_neg at ha'
  have hb2 := h_mono (a := 2) (b := b) (by norm_num) hb
  have hla : log a ≤ a - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hq : (a - 1 / 2) * log a ≤ (a - 1 / 2) * (a - 1) :=
    mul_le_mul_of_nonneg_left hla (by linarith)
  have hq2 : (a - 1 / 2) * (a - 1) - a ≤ -1 := by nlinarith
  have h2 : -1 ≤ 2 * log 2 - 2 - log 2 / 2 := by
    have := Real.log_two_gt_d9
    linarith
  have e : (a - 1 / 2) * log a = a * log a - log a / 2 := by ring
  linarith

/- English proof (translation)
Take `⟨m, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hn`. Establish `h1 : Stirling.stirlingSeq (m + 1) ≤ Stirling.stirlingSeq 1` using `Stirling.stirlingSeq'_antitone (Nat.zero_le m)`. Establish `hpos` using `Stirling.stirlingSeq'_pos m`. Establish `h2` using `Real.log_le_log hpos h1`. Rewrite `h2` using `[Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one, Real.log_div (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_sqrt (by norm_num)]`.

Establish `hm : (0 : ℝ) < ((m + 1 : ℕ) : ℝ)` using `by positivity`. Rewrite `h2` using `[Real.log_mul (by norm_num) hm.ne', Real.log_div hm.ne' (Real.exp_pos 1).ne', Real.log_exp]`. Move the coercions through the operations in `at h2 ⊢`. Use polynomial arithmetic with `[h2]`.
-/
theorem log_factorial_le {n : ℕ} (hn : n ≠ 0) :
    log ((n ! : ℕ) : ℝ) ≤ n * log n - n + log n / 2 + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h1 : Stirling.stirlingSeq (m + 1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  have hpos := Stirling.stirlingSeq'_pos m
  have h2 := Real.log_le_log hpos h1
  rw [Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one,
    Real.log_div (Real.exp_pos 1).ne' (by positivity), Real.log_exp,
    Real.log_sqrt (by norm_num)] at h2
  have hm : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [Real.log_mul (by norm_num) hm.ne', Real.log_div hm.ne' (Real.exp_pos 1).ne',
    Real.log_exp] at h2
  push_cast at h2 ⊢
  nlinarith [h2]

/- English proof (translation)
Rewrite using `[Real.le_log_iff_exp_le (by positivity)]`. Establish `he` using `Real.exp_one_lt_d9`. Establish `h15 : (6 : ℝ) / 5 ≤ Real.exp (1 / 5)`. Use `Real.add_one_le_exp (1 / 5 : ℝ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hsplit : Real.exp (9 / 5) * Real.exp (1 / 5) = Real.exp 1 * Real.exp 1`. Rewrite using `[← Real.exp_add, ← Real.exp_add]`. Evaluate the numerical expressions. Establish `hpi` using `Real.pi_gt_d2`. Establish `hpos : 0 < Real.exp (9 / 5)` using `Real.exp_pos _`.

Establish `he2 : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286` using `mul_self_lt_mul_self (Real.exp_pos 1).le he`. Establish `h3 : Real.exp (9 / 5) * (6 / 5) ≤ Real.exp (9 / 5) * Real.exp (1 / 5)` using `mul_le_mul_of_nonneg_left h15 hpos.le`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem log_two_pi_ge : (9 : ℝ) / 5 ≤ log (2 * π) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have he := Real.exp_one_lt_d9
  have h15 : (6 : ℝ) / 5 ≤ Real.exp (1 / 5) := by
    have := Real.add_one_le_exp (1 / 5 : ℝ)
    linarith
  have hsplit : Real.exp (9 / 5) * Real.exp (1 / 5) = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  have hpi := Real.pi_gt_d2
  have hpos : 0 < Real.exp (9 / 5) := Real.exp_pos _
  have he2 : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 :=
    mul_self_lt_mul_self (Real.exp_pos 1).le he
  have h3 : Real.exp (9 / 5) * (6 / 5) ≤ Real.exp (9 / 5) * Real.exp (1 / 5) :=
    mul_le_mul_of_nonneg_left h15 hpos.le
  nlinarith

/- English proof (translation)
Rewrite using `[Real.le_log_iff_exp_le (by norm_num)]`. Establish `he` using `Real.exp_one_lt_d9`. Establish `hsplit : Real.exp (33 / 10) = Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp (3 / 10)`. Rewrite using `[← Real.exp_add, ← Real.exp_add, ← Real.exp_add]`. Evaluate the numerical expressions.

Establish `hm : Real.exp (3 / 10) * Real.exp (-3 / 10) = 1`. Rewrite using `[← Real.exp_add]`. Evaluate the numerical expressions. Establish `h1 : (7 : ℝ) / 10 ≤ Real.exp (-3 / 10)`. Use `Real.add_one_le_exp (-3 / 10 : ℝ)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h310 : Real.exp (3 / 10) ≤ 10 / 7`. Establish `hp` using `Real.exp_pos (3 / 10)`. Use the polynomial consequences of the given equalities and inequalities. Establish `he2 : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286` using `mul_self_lt_mul_self (Real.exp_pos 1).le he`.

Establish `he3 : Real.exp 1 * Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 * 2.7182818286` using `mul_lt_mul'' he2 he (by positivity) (Real.exp_pos 1).le`. Rewrite using `[hsplit]`. Establish `h4 : Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp (3 / 10) ≤ (2.7182818286 * 2.7182818286 * 2.7182818286) * (10 / 7)` using `mul_le_mul he3.le h310 (Real.exp_pos _).le (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_thirty_ge : (33 : ℝ) / 10 ≤ log 30 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have he := Real.exp_one_lt_d9
  have hsplit : Real.exp (33 / 10) = Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp (3 / 10) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    norm_num
  have hm : Real.exp (3 / 10) * Real.exp (-3 / 10) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have h1 : (7 : ℝ) / 10 ≤ Real.exp (-3 / 10) := by
    have := Real.add_one_le_exp (-3 / 10 : ℝ)
    linarith
  have h310 : Real.exp (3 / 10) ≤ 10 / 7 := by
    have hp := Real.exp_pos (3 / 10)
    nlinarith
  have he2 : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 :=
    mul_self_lt_mul_self (Real.exp_pos 1).le he
  have he3 : Real.exp 1 * Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 * 2.7182818286 :=
    mul_lt_mul'' he2 he (by positivity) (Real.exp_pos 1).le
  rw [hsplit]
  have h4 : Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp (3 / 10) ≤
      (2.7182818286 * 2.7182818286 * 2.7182818286) * (10 / 7) :=
    mul_le_mul he3.le h310 (Real.exp_pos _).le (by norm_num)
  linarith

/- English proof (translation)
Introduce `y hy`. Simplify using `only [lf]`. Establish `hn1 : 1 ≤ ⌊y⌋₊` using `Nat.le_floor (by simpa using hy)`. Establish `hny : (⌊y⌋₊ : ℝ) ≤ y` using `Nat.floor_le (by linarith)`. Establish `h` using `log_factorial_le (n := ⌊y⌋₊) (by omega)`.

Establish `hn1' : (1 : ℝ) ≤ ⌊y⌋₊` using `by exact_mod_cast hn1`. Establish `hg` using `g_mono hn1' hny`. Establish `hl` using `Real.log_le_log (by linarith) hny`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lfUpper : LfUpper := by
  intro y hy
  simp only [lf]
  have hn1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hy)
  have hny : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have h := log_factorial_le (n := ⌊y⌋₊) (by omega)
  have hn1' : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hn1
  have hg := g_mono hn1' hny
  have hl := Real.log_le_log (by linarith) hny
  linarith

/- English proof (translation)
Introduce `y hy`. Simplify using `only [lf]`. Establish `hn1 : 1 ≤ ⌊y⌋₊` using `Nat.le_floor (by simpa using hy)`. Establish `hn1' : (1 : ℝ) ≤ ⌊y⌋₊` using `by exact_mod_cast hn1`. Establish `hy' : y ≤ (⌊y⌋₊ : ℝ) + 1` using `(Nat.lt_floor_add_one y).le`.

Establish `hS` using `Stirling.le_log_factorial_stirling (n := ⌊y⌋₊ + 1) (Nat.succ_ne_zero _)`. Establish `hfac : Real.log (((⌊y⌋₊ + 1) ! : ℕ) : ℝ) = Real.log ((⌊y⌋₊ : ℝ) + 1) + Real.log ((⌊y⌋₊ ! : ℕ) : ℝ)`. Rewrite using `[Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2π` using `log_two_pi_ge`. Establish `hh` using `h_le hy hy' (by linarith)`. Move the coercions through the operations in `at hS hfac`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lfLower : LfLower := by
  intro y hy
  simp only [lf]
  have hn1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hy)
  have hn1' : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hn1
  have hy' : y ≤ (⌊y⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one y).le
  have hS := Stirling.le_log_factorial_stirling (n := ⌊y⌋₊ + 1) (Nat.succ_ne_zero _)
  have hfac : Real.log (((⌊y⌋₊ + 1) ! : ℕ) : ℝ) =
      Real.log ((⌊y⌋₊ : ℝ) + 1) + Real.log ((⌊y⌋₊ ! : ℕ) : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    push_cast
    ring
  have h2π := log_two_pi_ge
  have hh := h_le hy hy' (by linarith)
  push_cast at hS hfac
  linarith

/- English proof (translation)
Establish `h2 : log (x / 2) = log x - log 2` using `Real.log_div hx.ne' (by norm_num)`. Establish `h3 : log (x / 3) = log x - log 3` using `Real.log_div hx.ne' (by norm_num)`. Establish `h5 : log (x / 5) = log x - log 5` using `Real.log_div hx.ne' (by norm_num)`. Establish `h30 : log (x / 30) = log x - log 30` using `Real.log_div hx.ne' (by norm_num)`. Rewrite using `[h2, h3, h5, h30]`.

Simplify using `only [chA]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main_term {x : ℝ} (hx : 0 < x) :
    (x * log x - x) - (x / 2 * log (x / 2) - x / 2) - (x / 3 * log (x / 3) - x / 3)
      - (x / 5 * log (x / 5) - x / 5) + (x / 30 * log (x / 30) - x / 30) = chA * x := by
  have h2 : log (x / 2) = log x - log 2 := Real.log_div hx.ne' (by norm_num)
  have h3 : log (x / 3) = log x - log 3 := Real.log_div hx.ne' (by norm_num)
  have h5 : log (x / 5) = log x - log 5 := Real.log_div hx.ne' (by norm_num)
  have h30 : log (x / 30) = log x - log 30 := Real.log_div hx.ne' (by norm_num)
  rw [h2, h3, h5, h30]
  simp only [chA]
  ring

/- English proof (translation)
Rewrite using `[show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]`.
-/
theorem stir_log_thirty : log 30 = log 2 + log 3 + log 5 := by
  rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]

/- English proof (translation)
Introduce `x hx`. Simplify using `only [chD]`. Establish `hx0 : (0 : ℝ) < x` using `by linarith`. Establish `l1` using `lfLower x (by linarith)`. Establish `l30` using `lfLower (x / 30) (by rw [le_div_iff₀ (by norm_num)]; linarith)`.

Establish `u2` using `lfUpper (x / 2) (by rw [le_div_iff₀ (by norm_num)]; linarith)`. Establish `u3` using `lfUpper (x / 3) (by rw [le_div_iff₀ (by norm_num)]; linarith)`. Establish `u5` using `lfUpper (x / 5) (by rw [le_div_iff₀ (by norm_num)]; linarith)`. Establish `hm` using `main_term hx0`. Establish `h2 : log (x / 2) = log x - log 2` using `Real.log_div hx0.ne' (by norm_num)`.

Establish `h3 : log (x / 3) = log x - log 3` using `Real.log_div hx0.ne' (by norm_num)`. Establish `h5 : log (x / 5) = log x - log 5` using `Real.log_div hx0.ne' (by norm_num)`. Establish `h30 : log (x / 30) = log x - log 30` using `Real.log_div hx0.ne' (by norm_num)`. Establish `hl30` using `log_thirty_ge`. Establish `hs` using `stir_log_thirty`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dLower : DLower := by
  intro x hx
  simp only [chD]
  have hx0 : (0 : ℝ) < x := by linarith
  have l1 := lfLower x (by linarith)
  have l30 := lfLower (x / 30) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have u2 := lfUpper (x / 2) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have u3 := lfUpper (x / 3) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have u5 := lfUpper (x / 5) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have hm := main_term hx0
  have h2 : log (x / 2) = log x - log 2 := Real.log_div hx0.ne' (by norm_num)
  have h3 : log (x / 3) = log x - log 3 := Real.log_div hx0.ne' (by norm_num)
  have h5 : log (x / 5) = log x - log 5 := Real.log_div hx0.ne' (by norm_num)
  have h30 : log (x / 30) = log x - log 30 := Real.log_div hx0.ne' (by norm_num)
  have hl30 := log_thirty_ge
  have hs := stir_log_thirty
  linarith

/- English proof (translation)
Introduce `x hx`. Simplify using `only [chD]`. Establish `hx0 : (0 : ℝ) < x` using `by linarith`. Establish `l1` using `lfUpper x (by linarith)`. Establish `l30` using `lfUpper (x / 30) (by rw [le_div_iff₀ (by norm_num)]; linarith)`.

Establish `u2` using `lfLower (x / 2) (by rw [le_div_iff₀ (by norm_num)]; linarith)`. Establish `u3` using `lfLower (x / 3) (by rw [le_div_iff₀ (by norm_num)]; linarith)`. Establish `u5` using `lfLower (x / 5) (by rw [le_div_iff₀ (by norm_num)]; linarith)`. Establish `hm` using `main_term hx0`. Establish `h2 : log (x / 2) = log x - log 2` using `Real.log_div hx0.ne' (by norm_num)`.

Establish `h3 : log (x / 3) = log x - log 3` using `Real.log_div hx0.ne' (by norm_num)`. Establish `h5 : log (x / 5) = log x - log 5` using `Real.log_div hx0.ne' (by norm_num)`. Establish `h30 : log (x / 30) = log x - log 30` using `Real.log_div hx0.ne' (by norm_num)`. Establish `hl30` using `log_thirty_ge`. Establish `hs` using `stir_log_thirty`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dUpper : DUpper := by
  intro x hx
  simp only [chD]
  have hx0 : (0 : ℝ) < x := by linarith
  have l1 := lfUpper x (by linarith)
  have l30 := lfUpper (x / 30) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have u2 := lfLower (x / 2) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have u3 := lfLower (x / 3) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have u5 := lfLower (x / 5) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have hm := main_term hx0
  have h2 : log (x / 2) = log x - log 2 := Real.log_div hx0.ne' (by norm_num)
  have h3 : log (x / 3) = log x - log 3 := Real.log_div hx0.ne' (by norm_num)
  have h5 : log (x / 5) = log x - log 5 := Real.log_div hx0.ne' (by norm_num)
  have h30 : log (x / 30) = log x - log 30 := Real.log_div hx0.ne' (by norm_num)
  have hl30 := log_thirty_ge
  have hs := stir_log_thirty
  linarith

end PI.PC
