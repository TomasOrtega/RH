import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn

open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk
open scoped InnerProductSpace

namespace GlobalTheory.Core.Rk

/- English proof (translation)
Establish `h1 : (2.7 : ℝ) < Real.exp 1` using `lt_trans (by norm_num) Real.exp_one_gt_d9`. Establish `h5 : Real.exp 5 = Real.exp 1 ^ 5`. Rewrite using `[← Real.exp_nat_mul]`. Evaluate the numerical expressions. Establish `h2 : (2.7 : ℝ) ^ 5 < Real.exp 1 ^ 5` using `pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)`.

Establish `h3 : (128 : ℝ) < Real.exp 5`. Rewrite using `[h5]; exact lt_trans (by norm_num) h2`. Rewrite using `[Real.exp_neg, one_div]`. Conclude with `inv_strictAnti₀ (by norm_num) h3`.
-/
theorem exp_neg_five_lt : Real.exp (-5) < 1 / 128 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : (2.7 : ℝ) ^ 5 < Real.exp 1 ^ 5 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have h3 : (128 : ℝ) < Real.exp 5 := by
    rw [h5]; exact lt_trans (by norm_num) h2
  rw [Real.exp_neg, one_div]
  exact inv_strictAnti₀ (by norm_num) h3

/- English proof (translation)
Establish `hk : 5 ≤ D.R.k`. Establish `h1` using `D.R.two_le_m`. Establish `h2` using `D.R.m_add_three_le_k`. Use linear arithmetic over natural numbers and integers. Establish `hf : 2 ≤ D.R.f`.

Establish `h1 : 0 < D.R.n` using `D.R.toFrame.ord_pos`. Establish `h2 : D.R.f = 2 * D.R.n` using `rfl`. Use linear arithmetic over natural numbers and integers. Establish `hkR : (5 : ℝ) ≤ (D.R.k : ℝ)` using `by exact_mod_cast hk`. Establish `hfR : (2 : ℝ) ≤ (D.R.f : ℝ)` using `by exact_mod_cast hf`.

Establish `hlog : 1 ≤ Real.log (D.R.k : ℝ)`. Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkf : (10 : ℝ) ≤ (D.R.k : ℝ) * D.R.f` using `by nlinarith`.

Establish `: (10 : ℝ) ≤ (D.R.k : ℝ) * D.R.f * Real.log (D.R.k : ℝ)` using `by nlinarith`. Unfold `kfk`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem five_le_half_kfk (D : D7) : 5 ≤ kfk D / 2 := by
  have hk : 5 ≤ D.R.k := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    omega
  have hf : 2 ≤ D.R.f := by
    have h1 : 0 < D.R.n := D.R.toFrame.ord_pos
    have h2 : D.R.f = 2 * D.R.n := rfl
    omega
  have hkR : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk
  have hfR : (2 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf
  have hlog : 1 ≤ Real.log (D.R.k : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hkf : (10 : ℝ) ≤ (D.R.k : ℝ) * D.R.f := by nlinarith
  have : (10 : ℝ) ≤ (D.R.k : ℝ) * D.R.f * Real.log (D.R.k : ℝ) := by nlinarith
  unfold kfk
  linarith

/- English proof (translation)
Introduce `D u L C hC hT`. Establish `hf : 2 ≤ D.R.f`. Establish `h1 : 0 < D.R.n` using `D.R.toFrame.ord_pos`. Establish `h2 : D.R.f = 2 * D.R.n` using `rfl`. Use linear arithmetic over natural numbers and integers.

Establish `hfR : (2 : ℝ) ≤ (D.R.f : ℝ)` using `by exact_mod_cast hf`. Establish `hTR : 4 * (D.R.f : ℝ) + 1 ≤ ((D.mem u).A.T : ℝ)` using `by exact_mod_cast hT`. Establish `hden : 0 < ((D.mem u).A.T : ℝ) - 1` using `by linarith`. Establish `hq : (D.R.f : ℝ) / (((D.mem u).A.T : ℝ) - 1) ≤ 1 / 4`. Rewrite using `[div_le_iff₀ hden]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5` using `exp_neg_five_lt`. Establish `hA : Real.exp (-(C * mfL D L)) ≤ Real.exp (-5)` using `Real.exp_le_exp.mpr (by linarith)`. Establish `hB : Real.exp (-(kfk D / 2)) ≤ Real.exp (-5)` using `Real.exp_le_exp.mpr (by linarith [five_le_half_kfk D])`. Unfold `eDiag`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem two_eDiag_lt : ∀ (D : D7) (u : D.what₂.Word) (L C : ℝ), 5 ≤ C * mfL D L → 4 * D.R.f + 1 ≤ (D.mem u).A.T → 2 * eDiag D L C < 1 - (D.R.f : ℝ) / (((D.mem u).A.T : ℝ) - 1) := by
  intro D u L C hC hT
  have hf : 2 ≤ D.R.f := by
    have h1 : 0 < D.R.n := D.R.toFrame.ord_pos
    have h2 : D.R.f = 2 * D.R.n := rfl
    omega
  have hfR : (2 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf
  have hTR : 4 * (D.R.f : ℝ) + 1 ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast hT
  have hden : 0 < ((D.mem u).A.T : ℝ) - 1 := by linarith
  have hq : (D.R.f : ℝ) / (((D.mem u).A.T : ℝ) - 1) ≤ 1 / 4 := by
    rw [div_le_iff₀ hden]
    linarith
  have h5 := exp_neg_five_lt
  have hA : Real.exp (-(C * mfL D L)) ≤ Real.exp (-5) :=
    Real.exp_le_exp.mpr (by linarith)
  have hB : Real.exp (-(kfk D / 2)) ≤ Real.exp (-5) :=
    Real.exp_le_exp.mpr (by linarith [five_le_half_kfk D])
  unfold eDiag
  linarith

end GlobalTheory.Core.Rk
