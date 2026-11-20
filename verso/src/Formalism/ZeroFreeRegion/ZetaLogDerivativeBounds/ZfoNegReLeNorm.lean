import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZfoTermReNonneg
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZfoGrowthBall

open Complex Metric

noncomputable section

namespace Formalism.ZF

/- English proof (translation)
Rewrite using `[Complex.neg_re]`. Conclude with `(neg_le_abs x.re).trans (Complex.abs_re_le_norm x)`.
-/
lemma zfo_neg_re_le_norm (x : ℂ) : (-x).re ≤ ‖x‖ := by
  rw [Complex.neg_re]
  exact (neg_le_abs x.re).trans (Complex.abs_re_le_norm x)

/- English proof (translation)
Take `⟨C, hC0, hC⟩` from `hLDR`. Use `⟨max 3 (Real.exp (3 * C)), le_max_left _ _, fun β t ht hzero => ?_⟩` and prove the remaining obligations. Establish `hT3 : 3 ≤ |t|` using `le_trans (le_max_left _ _) ht`. Establish `hTe : Real.exp (3 * C) ≤ |t|` using `le_trans (le_max_right _ _) ht`. Take `⟨L, hLdef⟩ : ∃ L, L = Real.log (|t| + 2)` from `⟨_, rfl⟩`.

Rewrite using `[← hLdef]`. Establish `hL1 : 1 < L`. Rewrite using `[hLdef, Real.lt_log_iff_exp_lt (by linarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hL0 : 0 < L` using `by linarith`. Establish `hLC : 3 * C ≤ L`. Rewrite using `[hLdef, Real.le_log_iff_exp_le (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hLT : L ≤ |t| + 2`.

Rewrite using `[hLdef]`. Use `Real.log_le_sub_one_of_pos (show 0 < |t| + 2 by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = 1 + (1 / 10000) / L` from `⟨_, rfl⟩`. Establish `hsm : 0 < (1 / 10000) / L` using `by positivity`.

Establish `hσ1 : 1 < σ` using `by rw [hσdef]; linarith`. Establish `hsm1 : (1 / 10000) / L ≤ 1`. Rewrite using `[div_le_one hL0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hσ2 : σ ≤ 2` using `by rw [hσdef]; linarith`.

Establish `hσinv : 1 / (σ - 1) = 10000 * L`. Rewrite using `[hσdef, show (1 : ℝ) + 1 / 10000 / L - 1 = (1 / 10000) / L by ring, one_div_div]`. Expand and normalize the polynomial expressions, which then agree. Establish `hσK : 2 / (σ - 1) ≤ 20000 * (|t| + 2)`. Establish `: 2 / (σ - 1) = 2 * (1 / (σ - 1))` using `by ring`.

Rewrite using `[this, hσinv]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hτ2 : 3 ≤ |2 * t|`. Rewrite using `[abs_mul]`. Evaluate the numerical expressions.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hτ2T : |2 * t| ≤ 2 * |t|`. Rewrite using `[abs_mul]`. Evaluate the numerical expressions. Establish `hM1 : (1 : ℝ) ≤ (|t| + 2) ^ 10` using `one_le_pow₀ (by linarith)`.

Take `⟨S1, hS10, hS1, hS1z⟩` from `zfo_landau hLL hσ1 hM1 (zfo_diff_ball hT3) (zfo_M_bound hG hI hσ1 hσ2 hσK hT3 hT3 (by linarith))`. Take `⟨S2, hS20, hS2, -⟩` from `zfo_landau hLL hσ1 hM1 (zfo_diff_ball hτ2) (zfo_M_bound hG hI hσ1 hσ2 hσK hT3 hτ2 hτ2T)`. Establish `e2 : ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) = (σ : ℂ) + 2 * t * I`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hS2` using `[e2]`. Establish `hlogM : Real.log ((|t| + 2) ^ 10) = 10 * L`. Rewrite using `[Real.log_pow, hLdef]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hS1`, `hS2` using `[hlogM]`. Establish `h341'` using `h341 σ t hσ1`. Establish `hR1 : (-(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ))).re ≤ 1 / (σ - 1) + C`. Establish `h` using `hC (σ : ℂ) (by simpa using hσ1)`. Simplify using `only [Complex.ofReal_re] at h`.

Conclude with `(zfo_neg_re_le_norm _).trans h`. Rewrite `hR1` using `[hσinv]`. Establish `hβσ : β < σ`. Use `zfo_zero_re_lt (ρ := (β : ℂ) + t * I) hσ1 hzero` as an intermediate fact. Simplify using `using this`.

Distinguish the cases in `hcase : σ - β ≤ 1 / 6`. Establish `hA` using `hS1z β hzero hcase`. Establish `hd : 0 < σ - β` using `by linarith`. Establish `key : 4 * (1 / (σ - β)) ≤ 37201 * L` using `by linarith`. Rewrite `key` using `[mul_one_div, div_le_iff₀ hd]`.

Establish `h3 : (21 / 200000) / L < σ - β`. Rewrite using `[div_lt_iff₀ hL0]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h4 : (21 / 200000) / L = (1 / 200000) / L + (1 / 10000) / L` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `push_neg at hcase`. Establish `h4 : (1 / 10000) / L ≤ 1 / 10000` using `div_le_self (by norm_num) hL1.le`. Establish `h5 : (1 / 200000) / L ≤ 1 / 200000` using `div_le_self (by norm_num) hL1.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma zfo_large (h341 : ThreeFourOne) (hLDR : LogDerivRight) (hG : ZetaGrowth)
    (hI : ZetaInvBound) (hLL : LandauLocal) :
    ∃ t₀ : ℝ, 3 ≤ t₀ ∧ ∀ β t : ℝ, t₀ ≤ |t| → riemannZeta ((β : ℂ) + t * I) = 0 →
      β < 1 - (1 / 200000) / Real.log (|t| + 2) := by
  obtain ⟨C, hC0, hC⟩ := hLDR
  refine ⟨max 3 (Real.exp (3 * C)), le_max_left _ _, fun β t ht hzero => ?_⟩
  have hT3 : 3 ≤ |t| := le_trans (le_max_left _ _) ht
  have hTe : Real.exp (3 * C) ≤ |t| := le_trans (le_max_right _ _) ht
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (|t| + 2) := ⟨_, rfl⟩
  rw [← hLdef]
  have hL1 : 1 < L := by
    rw [hLdef, Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hL0 : 0 < L := by linarith
  have hLC : 3 * C ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hLT : L ≤ |t| + 2 := by
    rw [hLdef]
    have := Real.log_le_sub_one_of_pos (show 0 < |t| + 2 by linarith)
    linarith
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = 1 + (1 / 10000) / L := ⟨_, rfl⟩
  have hsm : 0 < (1 / 10000) / L := by positivity
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hsm1 : (1 / 10000) / L ≤ 1 := by
    rw [div_le_one hL0]
    linarith
  have hσ2 : σ ≤ 2 := by rw [hσdef]; linarith
  have hσinv : 1 / (σ - 1) = 10000 * L := by
    rw [hσdef, show (1 : ℝ) + 1 / 10000 / L - 1 = (1 / 10000) / L by ring, one_div_div]
    ring
  have hσK : 2 / (σ - 1) ≤ 20000 * (|t| + 2) := by
    have : 2 / (σ - 1) = 2 * (1 / (σ - 1)) := by ring
    rw [this, hσinv]
    linarith
  have hτ2 : 3 ≤ |2 * t| := by
    rw [abs_mul]
    norm_num
    linarith
  have hτ2T : |2 * t| ≤ 2 * |t| := by
    rw [abs_mul]
    norm_num
  have hM1 : (1 : ℝ) ≤ (|t| + 2) ^ 10 := one_le_pow₀ (by linarith)
  obtain ⟨S1, hS10, hS1, hS1z⟩ := zfo_landau hLL hσ1 hM1 (zfo_diff_ball hT3)
    (zfo_M_bound hG hI hσ1 hσ2 hσK hT3 hT3 (by linarith))
  obtain ⟨S2, hS20, hS2, -⟩ := zfo_landau hLL hσ1 hM1 (zfo_diff_ball hτ2)
    (zfo_M_bound hG hI hσ1 hσ2 hσK hT3 hτ2 hτ2T)
  have e2 : ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) = (σ : ℂ) + 2 * t * I := by
    push_cast
    ring
  rw [e2] at hS2
  have hlogM : Real.log ((|t| + 2) ^ 10) = 10 * L := by
    rw [Real.log_pow, hLdef]
    push_cast
    ring
  rw [hlogM] at hS1 hS2
  have h341' := h341 σ t hσ1
  have hR1 : (-(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ))).re ≤ 1 / (σ - 1) + C := by
    have h := hC (σ : ℂ) (by simpa using hσ1)
    simp only [Complex.ofReal_re] at h
    exact (zfo_neg_re_le_norm _).trans h
  rw [hσinv] at hR1
  have hβσ : β < σ := by
    have := zfo_zero_re_lt (ρ := (β : ℂ) + t * I) hσ1 hzero
    simpa using this
  by_cases hcase : σ - β ≤ 1 / 6
  · have hA := hS1z β hzero hcase
    have hd : 0 < σ - β := by linarith
    have key : 4 * (1 / (σ - β)) ≤ 37201 * L := by linarith
    rw [mul_one_div, div_le_iff₀ hd] at key
    have h3 : (21 / 200000) / L < σ - β := by
      rw [div_lt_iff₀ hL0]
      nlinarith
    have h4 : (21 / 200000) / L = (1 / 200000) / L + (1 / 10000) / L := by ring
    linarith
  · push_neg at hcase
    have h4 : (1 / 10000) / L ≤ 1 / 10000 := div_le_self (by norm_num) hL1.le
    have h5 : (1 / 200000) / L ≤ 1 / 200000 := div_le_self (by norm_num) hL1.le
    linarith

end Formalism.ZF
