import Formalism.JumpKernelCokernel.Statement

namespace Formalism.KernelCokernelLengths.ThicknessSecondBoundLogLemmas

/- English proof (translation)
Establish `h : (11 : ℝ) ≤ ℓ` using `by exact_mod_cast hℓ`. Establish `hpos : 0 < ((ℓ : ℝ) - 1) ^ 2` using `by nlinarith`. Rewrite using `[div_le_div_iff₀ hpos (by norm_num)]`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr h) (by linarith : (0 : ℝ) ≤ 21 * ℓ - 11)]`.
-/
lemma coef_le (ℓ : ℕ) (hℓ : 11 ≤ ℓ) :
    (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 ≤ 21 / 100 := by
  have h : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hpos : 0 < ((ℓ : ℝ) - 1) ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hpos (by norm_num)]
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (by linarith : (0 : ℝ) ≤ 21 * ℓ - 11)]

/- English proof (translation)
Establish `h1` using `Real.log_le_sub_one_of_pos (show 0 < x / 100 by positivity)`. Establish `h2` using `Real.log_le_sub_one_of_pos (show (0 : ℝ) < 100 by norm_num)`. Establish `h3 : Real.log x = Real.log (x / 100) + Real.log 100`. Rewrite using `[← Real.log_mul (by positivity) (by norm_num)]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma log_two_le (x : ℝ) (hx : 0 < x) : Real.log x ≤ x / 100 + 98 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 100 by positivity)
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 100 by norm_num)
  have h3 : Real.log x = Real.log (x / 100) + Real.log 100 := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    congr 1
    field_simp
  linarith

/- English proof (translation)
Establish `h : (11 : ℝ) ≤ ℓ` using `by exact_mod_cast hℓ`. Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma one_le_log (ℓ : ℕ) (hℓ : 11 ≤ ℓ) : 1 ≤ Real.log (ℓ : ℝ) := by
  have h : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/- English proof (translation)
Conclude with `div_le_self (Real.log_nonneg hx) (one_le_log ℓ hℓ)`.
-/
lemma logb_le (ℓ : ℕ) (hℓ : 11 ≤ ℓ) (x : ℝ) (hx : 1 ≤ x) :
    Real.logb (ℓ : ℝ) x ≤ Real.log x := by
  exact div_le_self (Real.log_nonneg hx) (one_le_log ℓ hℓ)

/- English proof (translation)
Establish `h : (1 : ℝ) < ℓ`. Establish `: (11 : ℝ) ≤ ℓ` using `by exact_mod_cast hℓ`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `Real.logb_nonneg h hx`.
-/
lemma logb_nonneg' (ℓ : ℕ) (hℓ : 11 ≤ ℓ) (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ Real.logb (ℓ : ℝ) x := by
  have h : (1 : ℝ) < ℓ := by
    have : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  exact Real.logb_nonneg h hx

end Formalism.KernelCokernelLengths.ThicknessSecondBoundLogLemmas

open Formalism.KernelCokernelLengths.ThicknessSecondBoundLogLemmas in
/- English proof (translation)
Use `⟨1 / 100, by norm_num, 10000, ?_⟩` and prove the remaining obligations. Introduce `ℓ hℓ b η S t bi h hb hη hS ht h1 h2 h3`. Establish `hbR : (10000 : ℝ) ≤ b` using `by exact_mod_cast hb`. Establish `hη' : 100 * η ≤ b`. Establish `: ((100 * η : ℕ) : ℝ) ≤ b` using `by push_cast; linarith`.

Conclude with `this` after adjusting the coercions. Establish `hS' : 100 * S ≤ b`. Establish `: ((100 * S : ℕ) : ℝ) ≤ b` using `by push_cast; linarith`. Conclude with `this` after adjusting the coercions. Establish `ht' : 100 * t ≤ b`.

Establish `: ((100 * t : ℕ) : ℝ) ≤ b` using `by push_cast; linarith`. Conclude with `this` after adjusting the coercions. Use `⟨by omega, by omega, ?_⟩` and prove the remaining obligations. Establish `hHn : h + (η + t + 1) ≤ b + 2 * η + 2 * t + S + 2` using `by omega`. Establish `hH1 : 1 ≤ h + (η + t + 1)` using `by omega`.

Establish `hHR : ((h + (η + t + 1) : ℕ) : ℝ) ≤ b + 2 * η + 2 * t + S + 2` using `by exact_mod_cast hHn`. Establish `hH1R : (1 : ℝ) ≤ ((h + (η + t + 1) : ℕ) : ℝ)` using `by exact_mod_cast hH1`. Establish `hbi : b ≤ bi + t + 1` using `h1`. Establish `hbiR : (b : ℝ) ≤ bi + t + 1` using `by exact_mod_cast hbi`. Use `set H : ℕ := h + (η + t + 1) with hHdef`.

Establish `hx1 : (1 : ℝ) ≤ 2 * (H : ℝ)` using `by linarith`. Establish `hlb` using `logb_le ℓ hℓ (2 * (H : ℝ)) hx1`. Establish `hlb0` using `logb_nonneg' ℓ hℓ (2 * (H : ℝ)) hx1`. Establish `hlog` using `log_two_le (2 * (H : ℝ)) (by linarith)`. Establish `hc` using `coef_le ℓ hℓ`.

Establish `hcoef0 : 0 ≤ (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2`. Establish `hl : (11 : ℝ) ≤ ℓ` using `by exact_mod_cast hℓ`. Apply the tactic sequence `apply div_nonneg <;> nlinarith`. Establish `hH0 : (0 : ℝ) ≤ H` using `by positivity`. Establish `hA : (H : ℝ) * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 ≤ (H : ℝ) * (21 / 100)`.

Rewrite using `[mul_div_assoc]`. Conclude with `mul_le_mul_of_nonneg_left hc hH0`. Establish `hA0 : 0 ≤ (H : ℝ) * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2`. Rewrite using `[mul_div_assoc]`. Check the signs of the components of the expression.

Establish `haR0 : 0 ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H`. Unfold `Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `haR : Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H ≤ (H : ℝ) * (21 / 100) + 4 + ((2 * (H : ℝ)) / 100 + 98)`. Unfold `Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hceil` using `Nat.ceil_lt_add_one haR0`. Establish `hηR : (100 : ℝ) * η ≤ b` using `by exact_mod_cast hη'`. Establish `hSR : (100 : ℝ) * S ≤ b` using `by exact_mod_cast hS'`. Establish `htR : (100 : ℝ) * t ≤ b` using `by exact_mod_cast ht'`.

Establish `key : ((2 * ⌈Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H⌉₊ + (η + t + 1) + 1 : ℕ) : ℝ) ≤ (bi : ℝ)`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `key` after adjusting the coercions.
-/
theorem Formalism.KernelCokernelLengths.thickness_second_bound : Formalism.KernelCokernelLengths.ThickB := by
  refine ⟨1 / 100, by norm_num, 10000, ?_⟩
  intro ℓ hℓ b η S t bi h hb hη hS ht h1 h2 h3
  have hbR : (10000 : ℝ) ≤ b := by exact_mod_cast hb
  have hη' : 100 * η ≤ b := by
    have : ((100 * η : ℕ) : ℝ) ≤ b := by push_cast; linarith
    exact_mod_cast this
  have hS' : 100 * S ≤ b := by
    have : ((100 * S : ℕ) : ℝ) ≤ b := by push_cast; linarith
    exact_mod_cast this
  have ht' : 100 * t ≤ b := by
    have : ((100 * t : ℕ) : ℝ) ≤ b := by push_cast; linarith
    exact_mod_cast this
  refine ⟨by omega, by omega, ?_⟩
  have hHn : h + (η + t + 1) ≤ b + 2 * η + 2 * t + S + 2 := by omega
  have hH1 : 1 ≤ h + (η + t + 1) := by omega
  have hHR : ((h + (η + t + 1) : ℕ) : ℝ) ≤ b + 2 * η + 2 * t + S + 2 := by exact_mod_cast hHn
  have hH1R : (1 : ℝ) ≤ ((h + (η + t + 1) : ℕ) : ℝ) := by exact_mod_cast hH1
  have hbi : b ≤ bi + t + 1 := h1
  have hbiR : (b : ℝ) ≤ bi + t + 1 := by exact_mod_cast hbi
  set H : ℕ := h + (η + t + 1) with hHdef
  have hx1 : (1 : ℝ) ≤ 2 * (H : ℝ) := by linarith
  have hlb := logb_le ℓ hℓ (2 * (H : ℝ)) hx1
  have hlb0 := logb_nonneg' ℓ hℓ (2 * (H : ℝ)) hx1
  have hlog := log_two_le (2 * (H : ℝ)) (by linarith)
  have hc := coef_le ℓ hℓ
  have hcoef0 : 0 ≤ (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
    have hl : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    apply div_nonneg <;> nlinarith
  have hH0 : (0 : ℝ) ≤ H := by positivity
  have hA : (H : ℝ) * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 ≤ (H : ℝ) * (21 / 100) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hc hH0
  have hA0 : 0 ≤ (H : ℝ) * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
    rw [mul_div_assoc]; positivity
  have haR0 : 0 ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H := by
    unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
    linarith
  have haR : Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H ≤ (H : ℝ) * (21 / 100) + 4 + ((2 * (H : ℝ)) / 100 + 98) := by
    unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
    linarith
  have hceil := Nat.ceil_lt_add_one haR0
  have hηR : (100 : ℝ) * η ≤ b := by exact_mod_cast hη'
  have hSR : (100 : ℝ) * S ≤ b := by exact_mod_cast hS'
  have htR : (100 : ℝ) * t ≤ b := by exact_mod_cast ht'
  have key : ((2 * ⌈Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H⌉₊ + (η + t + 1) + 1 : ℕ) : ℝ) ≤ (bi : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast key
