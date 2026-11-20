import Formalism.JumpKernelCokernel.Statement

namespace Formalism.KernelCokernelLengths.ThicknessFirstBoundLogLemmas

open Filter

/- English proof (translation)
Rewrite using `[div_le_iff₀ (by nlinarith : (0 : ℝ) < (x - 1) ^ 2)]`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hx) (by linarith : (0 : ℝ) ≤ x - 11 / 21)]`.
-/
lemma coef_le (x : ℝ) (hx : 11 ≤ x) : (2 * x - 1) / (x - 1) ^ 2 ≤ 21 / 100 := by
  rw [div_le_iff₀ (by nlinarith : (0 : ℝ) < (x - 1) ^ 2)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (by linarith : (0 : ℝ) ≤ x - 11 / 21)]

/- English proof (translation)
Conclude with `div_nonneg (by linarith) (sq_nonneg _)`.
-/
lemma coef_nonneg (x : ℝ) (hx : 11 ≤ x) : 0 ≤ (2 * x - 1) / (x - 1) ^ 2 := by
  exact div_nonneg (by linarith) (sq_nonneg _)

/- English proof (translation)
Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`. Combine the linear relations using `[Real.exp_one_lt_d9]`.
-/
lemma one_le_log (x : ℝ) (hx : 11 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

/- English proof (translation)
Rewrite using `[Real.logb]`. Conclude with `div_le_self (Real.log_nonneg hy) (one_le_log x hx)`.
-/
lemma logb_le (x y : ℝ) (hx : 11 ≤ x) (hy : 1 ≤ y) : Real.logb x y ≤ Real.log y := by
  rw [Real.logb]
  exact div_le_self (Real.log_nonneg hy) (one_le_log x hx)

/- English proof (translation)
Rewrite using `[Real.logb]`. Conclude with `div_nonneg (Real.log_nonneg hy) (by linarith [one_le_log x hx])`.
-/
lemma logb_nonneg' (x y : ℝ) (hx : 11 ≤ x) (hy : 1 ≤ y) : 0 ≤ Real.logb x y := by
  rw [Real.logb]
  exact div_nonneg (Real.log_nonneg hy) (by linarith [one_le_log x hx])

/- English proof (translation)
Use `⟨⌈256 / c ^ 2 + 26 / c⌉₊ + 1, fun n hn => ?_⟩` and prove the remaining obligations. Establish `hA : 0 ≤ 256 / c ^ 2` using `by positivity`. Establish `hB : 0 ≤ 26 / c` using `by positivity`. Establish `hnR : 256 / c ^ 2 + 26 / c + 1 ≤ (n : ℝ)`. Establish `h1` using `Nat.le_ceil (256 / c ^ 2 + 26 / c)`.

Establish `h2 : ((⌈256 / c ^ 2 + 26 / c⌉₊ + 1 : ℕ) : ℝ) ≤ n` using `by exact_mod_cast hn`. Move the coercions through the operations in `at h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn0 : (0 : ℝ) < n` using `by linarith`. Establish `hlog : Real.log (4 * n) ≤ 2 * Real.sqrt (4 * n)`.

Establish `h` using `Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 4 * n))`. Rewrite `h` using `[Real.log_sqrt (by positivity)]`. Combine the linear relations using `[Real.sqrt_nonneg (4 * (n : ℝ))]`. Establish `hsq : Real.sqrt (4 * n) = 2 * Real.sqrt n`. Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]`.

Establish `hs0 : 0 ≤ Real.sqrt n` using `Real.sqrt_nonneg _`. Establish `hss : Real.sqrt n * Real.sqrt n = n` using `Real.mul_self_sqrt hn0.le`. Establish `hs16 : 16 / c ≤ Real.sqrt n`. Establish `h1 : (16 / c) ^ 2 ≤ (n : ℝ)`. Establish `: (16 / c) ^ 2 = 256 / c ^ 2` using `by ring`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Establish `h16 : 16 ≤ c * Real.sqrt n`. Rewrite `hs16` using `[div_le_iff₀ hc]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h26 : 26 ≤ c * n`. Establish `: 26 / c ≤ (n : ℝ)` using `by linarith`. Rewrite `this` using `[div_le_iff₀ hc]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcn : c * n = (c * Real.sqrt n) * Real.sqrt n` using `by rw [mul_assoc, hss]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right h16 hs0]`.
-/
lemma eventually_log (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 13 + 2 * Real.log (4 * (n : ℝ)) ≤ c * n := by
  refine ⟨⌈256 / c ^ 2 + 26 / c⌉₊ + 1, fun n hn => ?_⟩
  have hA : 0 ≤ 256 / c ^ 2 := by positivity
  have hB : 0 ≤ 26 / c := by positivity
  have hnR : 256 / c ^ 2 + 26 / c + 1 ≤ (n : ℝ) := by
    have h1 := Nat.le_ceil (256 / c ^ 2 + 26 / c)
    have h2 : ((⌈256 / c ^ 2 + 26 / c⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : Real.log (4 * n) ≤ 2 * Real.sqrt (4 * n) := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 4 * n))
    rw [Real.log_sqrt (by positivity)] at h
    linarith [Real.sqrt_nonneg (4 * (n : ℝ))]
  have hsq : Real.sqrt (4 * n) = 2 * Real.sqrt n := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hs0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hs16 : 16 / c ≤ Real.sqrt n := by
    have h1 : (16 / c) ^ 2 ≤ (n : ℝ) := by
      have : (16 / c) ^ 2 = 256 / c ^ 2 := by ring
      linarith
    calc 16 / c = Real.sqrt ((16 / c) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt h1
  have h16 : 16 ≤ c * Real.sqrt n := by
    rw [div_le_iff₀ hc] at hs16
    linarith
  have h26 : 26 ≤ c * n := by
    have : 26 / c ≤ (n : ℝ) := by linarith
    rw [div_le_iff₀ hc] at this
    linarith
  have hcn : c * n = (c * Real.sqrt n) * Real.sqrt n := by rw [mul_assoc, hss]
  nlinarith [mul_le_mul_of_nonneg_right h16 hs0]

end Formalism.KernelCokernelLengths.ThicknessFirstBoundLogLemmas

open Formalism.KernelCokernelLengths.ThicknessFirstBoundLogLemmas in
/- English proof (translation)
Introduce `ε hε`. Take `⟨N, hN⟩` from `eventually_log (ε / 2) (by linarith)`. Use `⟨min (1 / 10) (ε / 10), by positivity, max N 4, ?_⟩` and prove the remaining obligations. Introduce `ℓ hℓ b η S t bi h hb hη hS ht h1 h2 h3`. Establish `hδ1 : min (1 / 10) (ε / 10) ≤ 1 / 10` using `min_le_left _ _`.

Establish `hδε : min (1 / 10) (ε / 10) ≤ ε / 10` using `min_le_right _ _`. Establish `hbN : N ≤ b` using `le_trans (le_max_left _ _) hb`. Establish `hb4 : 4 ≤ b` using `le_trans (le_max_right _ _) hb`. Establish `hb0 : (0 : ℝ) ≤ b` using `Nat.cast_nonneg _`. Establish `hb4R : (4 : ℝ) ≤ b` using `by exact_mod_cast hb4`.

Establish `hℓ' : (11 : ℝ) ≤ ℓ` using `by exact_mod_cast hℓ`. Establish `hH1 : (1 : ℝ) ≤ 2 * ((h + (η + t + 1) : ℕ) : ℝ)`. Establish `: 1 ≤ h + (η + t + 1)` using `by omega`. Establish `: (1 : ℝ) ≤ ((h + (η + t + 1) : ℕ) : ℝ)` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hHle : ((h + (η + t + 1) : ℕ) : ℝ) ≤ b + 2 * η + 2 * t + S + 2`. Establish `: h + (η + t + 1) ≤ b + 2 * η + 2 * t + S + 2` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hδb : min (1 / 10) (ε / 10) * (b : ℝ) ≤ ε / 10 * b` using `mul_le_mul_of_nonneg_right hδε hb0`. Establish `hδb1 : min (1 / 10) (ε / 10) * (b : ℝ) ≤ 1 / 10 * b` using `mul_le_mul_of_nonneg_right hδ1 hb0`.

Establish `hcoef` using `coef_le ℓ hℓ'`. Establish `hcoef0` using `coef_nonneg ℓ hℓ'`. Establish `hlogb` using `logb_le ℓ (2 * ((h + (η + t + 1) : ℕ) : ℝ)) hℓ' hH1`. Establish `hlogb0` using `logb_nonneg' ℓ (2 * ((h + (η + t + 1) : ℕ) : ℝ)) hℓ' hH1`. Establish `h2H : 2 * ((h + (η + t + 1) : ℕ) : ℝ) ≤ 4 * b`.

Establish `hη' : (η : ℝ) ≤ 1 / 10 * b` using `le_trans hη hδb1`. Establish `hS' : (S : ℝ) ≤ 1 / 10 * b` using `le_trans hS hδb1`. Establish `ht' : (t : ℝ) ≤ 1 / 10 * b` using `le_trans ht hδb1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog2H : Real.log (2 * ((h + (η + t + 1) : ℕ) : ℝ)) ≤ Real.log (4 * b)` using `Real.log_le_log (by linarith) h2H`.

Establish `hlogN` using `hN b hbN`. Establish `haR : Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1)) = ((h + (η + t + 1) : ℕ) : ℝ) * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2) + 3 + (Real.logb (ℓ : ℝ) (2 * ((h + (η + t + 1) : ℕ) : ℝ)) + 1)`. Unfold `Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam`. Rewrite using `[mul_div_assoc]`. Establish `hHc : ((h + (η + t + 1) : ℕ) : ℝ) * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2) ≤ ((h + (η + t + 1) : ℕ) : ℝ) * (21 / 100)` using `mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg _)`.

Establish `haR0 : 0 ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1))`. Rewrite using `[haR]`. Use `mul_nonneg (Nat.cast_nonneg (h + (η + t + 1))) hcoef0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hceil : (⌈Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1))⌉₊ : ℝ) ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1)) + 1` using `(Nat.ceil_lt_add_one haR0).le`.

Establish `hεb : 0 ≤ ε * (b : ℝ)` using `mul_nonneg hε.le hb0`. Use `push_cast`. Move the coercions through the operations in `at hHle hHc hceil haR hlogb hlog2H`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Formalism.KernelCokernelLengths.thickness_first_bound : Formalism.KernelCokernelLengths.ThickA := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_log (ε / 2) (by linarith)
  refine ⟨min (1 / 10) (ε / 10), by positivity, max N 4, ?_⟩
  intro ℓ hℓ b η S t bi h hb hη hS ht h1 h2 h3
  have hδ1 : min (1 / 10) (ε / 10) ≤ 1 / 10 := min_le_left _ _
  have hδε : min (1 / 10) (ε / 10) ≤ ε / 10 := min_le_right _ _
  have hbN : N ≤ b := le_trans (le_max_left _ _) hb
  have hb4 : 4 ≤ b := le_trans (le_max_right _ _) hb
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hb4R : (4 : ℝ) ≤ b := by exact_mod_cast hb4
  have hℓ' : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hH1 : (1 : ℝ) ≤ 2 * ((h + (η + t + 1) : ℕ) : ℝ) := by
    have : 1 ≤ h + (η + t + 1) := by omega
    have : (1 : ℝ) ≤ ((h + (η + t + 1) : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hHle : ((h + (η + t + 1) : ℕ) : ℝ) ≤ b + 2 * η + 2 * t + S + 2 := by
    have : h + (η + t + 1) ≤ b + 2 * η + 2 * t + S + 2 := by omega
    exact_mod_cast this
  have hδb : min (1 / 10) (ε / 10) * (b : ℝ) ≤ ε / 10 * b := mul_le_mul_of_nonneg_right hδε hb0
  have hδb1 : min (1 / 10) (ε / 10) * (b : ℝ) ≤ 1 / 10 * b := mul_le_mul_of_nonneg_right hδ1 hb0
  have hcoef := coef_le ℓ hℓ'
  have hcoef0 := coef_nonneg ℓ hℓ'
  have hlogb := logb_le ℓ (2 * ((h + (η + t + 1) : ℕ) : ℝ)) hℓ' hH1
  have hlogb0 := logb_nonneg' ℓ (2 * ((h + (η + t + 1) : ℕ) : ℝ)) hℓ' hH1
  have h2H : 2 * ((h + (η + t + 1) : ℕ) : ℝ) ≤ 4 * b := by
    have hη' : (η : ℝ) ≤ 1 / 10 * b := le_trans hη hδb1
    have hS' : (S : ℝ) ≤ 1 / 10 * b := le_trans hS hδb1
    have ht' : (t : ℝ) ≤ 1 / 10 * b := le_trans ht hδb1
    linarith
  have hlog2H : Real.log (2 * ((h + (η + t + 1) : ℕ) : ℝ)) ≤ Real.log (4 * b) :=
    Real.log_le_log (by linarith) h2H
  have hlogN := hN b hbN
  have haR : Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1)) =
      ((h + (η + t + 1) : ℕ) : ℝ) * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2) + 3 +
        (Real.logb (ℓ : ℝ) (2 * ((h + (η + t + 1) : ℕ) : ℝ)) + 1) := by
    unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
    rw [mul_div_assoc]
  have hHc : ((h + (η + t + 1) : ℕ) : ℝ) * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2) ≤
      ((h + (η + t + 1) : ℕ) : ℝ) * (21 / 100) :=
    mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg _)
  have haR0 : 0 ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1)) := by
    rw [haR]
    have := mul_nonneg (Nat.cast_nonneg (h + (η + t + 1))) hcoef0
    linarith
  have hceil : (⌈Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1))⌉₊ : ℝ) ≤
      Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1)) + 1 := (Nat.ceil_lt_add_one haR0).le
  have hεb : 0 ≤ ε * (b : ℝ) := mul_nonneg hε.le hb0
  push_cast
  push_cast at hHle hHc hceil haR hlogb hlog2H
  linarith
