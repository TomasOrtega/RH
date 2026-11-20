import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty

open GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG

/- English proof (translation)
Introduce `eps CD heps _heps' hCD C hC`. Use `⟨max (max 1 (C + 2)) (max (C ^ (100 / eps)) ((16 : ℝ) ^ (2 / eps))), ?_⟩` and prove the remaining obligations. Introduce `x hx m f k lrd Del h r hkr hrk`. Establish `hx1 : 1 ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `hxC : C + 2 ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`.

Establish `hxC' : C ^ (100 / eps) ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx`. Establish `hx16 : (16 : ℝ) ^ (2 / eps) ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx`. Establish `hx0 : 0 ≤ x` using `by linarith`. Establish `hm1 : 1 ≤ m` using `le_trans (Real.one_le_rpow hx1 (by norm_num)) h.m_lo`. Establish `hm4 : x ≤ m ^ 4`.

Establish `h1 : (x ^ ((1 : ℝ) / 4)) ^ 4 ≤ m ^ 4` using `by gcongr`. Conclude with `h.m_lo`. Establish `h2 : (x ^ ((1 : ℝ) / 4)) ^ 4 = x`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hx0]`. Evaluate the numerical expressions.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hf : x ≤ f` using `le_trans hm4 h.mf`. Establish `hk : x ≤ k` using `le_trans hf h.fk`. Establish `hr : x ≤ r` using `le_trans hk hkr`. Establish `hf1 : 1 ≤ f` using `by linarith`.

Establish `hk1 : 1 ≤ k` using `by linarith`. Establish `hr1 : 1 ≤ r` using `by linarith`. Establish `hL : 1 ≤ x ^ eps` using `Real.one_le_rpow hx1 heps.le`. Establish `hL' : 1 ≤ x ^ (eps / 100)` using `Real.one_le_rpow hx1 (by positivity)`. Establish `hm10 : m ^ 10 ≤ f ^ 3`.

Establish `h1 : m ^ 10 ≤ m ^ 12` using `pow_le_pow_right₀ hm1 (by norm_num)`. Establish `h2 : m ^ 12 = (m ^ 4) ^ 3` using `by ring`. Establish `h3 : (m ^ 4) ^ 3 ≤ f ^ 3` using `by gcongr; exact h.mf`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hf3 : f ≤ f ^ 3`.

Use `pow_le_pow_right₀ hf1 (show 1 ≤ 3 by norm_num); simpa using this` as an intermediate fact. Establish `hS : C * k * m ^ 4 + r * m ^ 10 ≤ (C + 2) * k * f ^ 3`. Establish `h1 : C * k * m ^ 4 ≤ C * k * f ^ 3`. Establish `: m ^ 4 ≤ f ^ 3` using `le_trans h.mf hf3`. Use `gcongr`.

Establish `h2 : r * m ^ 10 ≤ (2 * k) * f ^ 3` using `by gcongr`. Use the polynomial consequences of the given equalities and inequalities. Establish `hSpos : 0 < C * k * m ^ 4 + r * m ^ 10` using `by positivity`. Establish `hy1 : 1 ≤ k * f * x ^ eps`. Establish `: 1 ≤ k * f` using `one_le_mul_of_one_le_of_one_le hk1 hf1`.

Conclude with `one_le_mul_of_one_le_of_one_le this hL`. Establish `hDel3 : (k * f * x ^ eps) ^ (3 : ℕ) ≤ Del`. Use `Real.rpow_le_rpow_of_exponent_le hy1 hCD` as an intermediate fact. Rewrite `this` using `[show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`. Combine the linear relations using `[h.Del_lo]`.

Establish `hDelpos : 0 < Del`. Establish `: 0 < (k * f * x ^ eps) ^ (3 : ℕ)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc1 : C * k * m ^ 4 + r * m ^ 10 < 4 * Del`. Establish `hkf3 : 0 < k * f ^ 3` using `by positivity`.

Establish `hk2 : C + 2 < 4 * k ^ 2` using `by nlinarith`. Establish `e1 : (C + 2) * k * f ^ 3 < 4 * k ^ 2 * (k * f ^ 3)` using `by nlinarith`. Establish `e2 : 4 * k ^ 2 * (k * f ^ 3) ≤ 4 * (k * f * x ^ eps) ^ (3 : ℕ)`. Establish `hkf : k * f ≤ k * f * x ^ eps` using `le_mul_of_one_le_right (by positivity) hL`. Establish `: (k * f) ^ 3 ≤ (k * f * x ^ eps) ^ 3` using `by gcongr`.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Use `set t := x ^ (eps / 2) with ht`. Establish `ht16 : 16 ≤ t`. Establish `h1 : ((16 : ℝ) ^ (2 / eps)) ^ (eps / 2) ≤ x ^ (eps / 2)` using `Real.rpow_le_rpow (by positivity) hx16 (by positivity)`.

Establish `h2 : ((16 : ℝ) ^ (2 / eps)) ^ (eps / 2) = 16`. Rewrite using `[← Real.rpow_mul (by norm_num)]`. Establish `: 2 / eps * (eps / 2) = 1` using `by field_simp`. Rewrite using `[this, Real.rpow_one]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hxe : x ^ eps = t ^ 2`. Rewrite using `[ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hDelE : Del ≤ Real.exp t`. Use `h.Del_hi` as an intermediate fact. Rewrite `this` using `[Real.log_le_iff_le_exp hDelpos]`. Conclude with `this`. Establish `hc2 : C * k * m ^ 4 + r * m ^ 10 < Real.sqrt (bx x eps)`.

Rewrite using `[Real.lt_sqrt hSpos.le]`. Establish `e1 : (C * k * m ^ 4 + r * m ^ 10) ^ 2 < (4 * Real.exp t) ^ 2`. Establish `: C * k * m ^ 4 + r * m ^ 10 < 4 * Real.exp t` using `by linarith`. Use `gcongr`. Establish `e2 : (4 * Real.exp t) ^ 2 = Real.exp (Real.log 16 + 2 * t)`.

Rewrite using `[Real.exp_add, Real.exp_log (by norm_num)]`. Rewrite using `[show 2 * t = t + t by ring, Real.exp_add]; ring`. Establish `e3 : Real.log 16 + 2 * t ≤ x ^ eps`. Establish `: Real.log 16 ≤ 16 - 1` using `Real.log_le_sub_one_of_pos (by norm_num)`. Rewrite using `[hxe]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `e4 : Real.exp (Real.log 16 + 2 * t) ≤ bx x eps`. Unfold `bx`. Conclude with `Real.exp_le_exp.mpr e3`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hc3 : C * k * m ^ 4 + r * m ^ 10 < x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps`. Establish `hf35 : f ^ 3 ≤ f ^ 5` using `pow_le_pow_right₀ hf1 (by norm_num)`. Establish `e1 : C * k * m ^ 4 + r * m ^ 10 ≤ (C + 2) * r * f ^ 5`. Establish `: (C + 2) * k * f ^ 3 ≤ (C + 2) * r * f ^ 5` using `by gcongr`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hx18 : x ≤ x ^ 18`. Use `pow_le_pow_right₀ hx1 (show 1 ≤ 18 by norm_num); simpa using this` as an intermediate fact. Establish `hr18 : x ^ 18 ≤ r ^ 18` using `by gcongr`. Establish `e2 : (C + 2) * r * f ^ 5 < r ^ 18 * (r * f ^ 5)`. Establish `hp : 0 < r * f ^ 5` using `by positivity`.

Establish `hC18 : C + 2 < r ^ 18`. Establish `hx2 : x ^ 2 ≤ x ^ 18` using `pow_le_pow_right₀ hx1 (by norm_num)`. Establish `: x < x ^ 2` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Use `mul_lt_mul_of_pos_right hC18 hp` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation. Establish `e3 : r ^ 18 * (r * f ^ 5) = r ^ 19 * f ^ 5` using `by ring`. Establish `e4 : r ^ 19 * f ^ 5 ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps`. Establish `hp : 0 ≤ r ^ 19 * f ^ 5` using `by positivity`. Establish `h1 : 1 ≤ x ^ (eps / 100) * x ^ eps` using `one_le_mul_of_one_le_of_one_le hL' hL`.

Use `mul_le_mul_of_nonneg_right h1 hp` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc4 : C * r ^ 19 * f ^ 5 * x ^ eps ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps`. Establish `hCx : C ≤ x ^ (eps / 100)`.

Establish `h1 : (C ^ (100 / eps)) ^ (eps / 100) ≤ x ^ (eps / 100)` using `Real.rpow_le_rpow (by positivity) hxC' (by positivity)`. Establish `h2 : (C ^ (100 / eps)) ^ (eps / 100) = C`. Rewrite using `[← Real.rpow_mul hC.le]`. Establish `: 100 / eps * (eps / 100) = 1` using `by field_simp`. Rewrite using `[this, Real.rpow_one]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp : 0 ≤ r ^ 19 * f ^ 5 * x ^ eps` using `by positivity`. Use `mul_le_mul_of_nonneg_right hCx hp` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨hc1, hc2, hc3, hc4⟩`.
-/
theorem gaps_exceed :
    ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x →
      ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → ∀ r : ℝ, k ≤ r → r ≤ 2 * k →
      C * k * m ^ 4 + r * m ^ 10 < 4 * Del ∧ C * k * m ^ 4 + r * m ^ 10 < Real.sqrt (bx x eps) ∧
      C * k * m ^ 4 + r * m ^ 10 < x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps ∧
      C * r ^ 19 * f ^ 5 * x ^ eps ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
  intro eps CD heps _heps' hCD C hC
  refine ⟨max (max 1 (C + 2)) (max (C ^ (100 / eps)) ((16 : ℝ) ^ (2 / eps))), ?_⟩
  intro x hx m f k lrd Del h r hkr hrk
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxC : C + 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxC' : C ^ (100 / eps) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx16 : (16 : ℝ) ^ (2 / eps) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 ≤ x := by linarith
  have hm1 : 1 ≤ m := le_trans (Real.one_le_rpow hx1 (by norm_num)) h.m_lo
  have hm4 : x ≤ m ^ 4 := by
    have h1 : (x ^ ((1 : ℝ) / 4)) ^ 4 ≤ m ^ 4 := by
      gcongr
      exact h.m_lo
    have h2 : (x ^ ((1 : ℝ) / 4)) ^ 4 = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
    linarith
  have hf : x ≤ f := le_trans hm4 h.mf
  have hk : x ≤ k := le_trans hf h.fk
  have hr : x ≤ r := le_trans hk hkr
  have hf1 : 1 ≤ f := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hL : 1 ≤ x ^ eps := Real.one_le_rpow hx1 heps.le
  have hL' : 1 ≤ x ^ (eps / 100) := Real.one_le_rpow hx1 (by positivity)
  have hm10 : m ^ 10 ≤ f ^ 3 := by
    have h1 : m ^ 10 ≤ m ^ 12 := pow_le_pow_right₀ hm1 (by norm_num)
    have h2 : m ^ 12 = (m ^ 4) ^ 3 := by ring
    have h3 : (m ^ 4) ^ 3 ≤ f ^ 3 := by gcongr; exact h.mf
    linarith
  have hf3 : f ≤ f ^ 3 := by
    have := pow_le_pow_right₀ hf1 (show 1 ≤ 3 by norm_num); simpa using this
  have hS : C * k * m ^ 4 + r * m ^ 10 ≤ (C + 2) * k * f ^ 3 := by
    have h1 : C * k * m ^ 4 ≤ C * k * f ^ 3 := by
      have : m ^ 4 ≤ f ^ 3 := le_trans h.mf hf3
      gcongr
    have h2 : r * m ^ 10 ≤ (2 * k) * f ^ 3 := by
      gcongr
    nlinarith
  have hSpos : 0 < C * k * m ^ 4 + r * m ^ 10 := by positivity

  have hy1 : 1 ≤ k * f * x ^ eps := by
    have : 1 ≤ k * f := one_le_mul_of_one_le_of_one_le hk1 hf1
    exact one_le_mul_of_one_le_of_one_le this hL
  have hDel3 : (k * f * x ^ eps) ^ (3 : ℕ) ≤ Del := by
    have := Real.rpow_le_rpow_of_exponent_le hy1 hCD
    rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    linarith [h.Del_lo]
  have hDelpos : 0 < Del := by
    have : 0 < (k * f * x ^ eps) ^ (3 : ℕ) := by positivity
    linarith
  have hc1 : C * k * m ^ 4 + r * m ^ 10 < 4 * Del := by
    have hkf3 : 0 < k * f ^ 3 := by positivity
    have hk2 : C + 2 < 4 * k ^ 2 := by nlinarith
    have e1 : (C + 2) * k * f ^ 3 < 4 * k ^ 2 * (k * f ^ 3) := by nlinarith
    have e2 : 4 * k ^ 2 * (k * f ^ 3) ≤ 4 * (k * f * x ^ eps) ^ (3 : ℕ) := by
      have hkf : k * f ≤ k * f * x ^ eps := le_mul_of_one_le_right (by positivity) hL
      have : (k * f) ^ 3 ≤ (k * f * x ^ eps) ^ 3 := by gcongr
      nlinarith
    linarith

  set t := x ^ (eps / 2) with ht
  have ht16 : 16 ≤ t := by
    have h1 : ((16 : ℝ) ^ (2 / eps)) ^ (eps / 2) ≤ x ^ (eps / 2) :=
      Real.rpow_le_rpow (by positivity) hx16 (by positivity)
    have h2 : ((16 : ℝ) ^ (2 / eps)) ^ (eps / 2) = 16 := by
      rw [← Real.rpow_mul (by norm_num)]
      have : 2 / eps * (eps / 2) = 1 := by field_simp
      rw [this, Real.rpow_one]
    linarith
  have hxe : x ^ eps = t ^ 2 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; congr 1; push_cast; ring
  have hDelE : Del ≤ Real.exp t := by
    have := h.Del_hi
    rw [Real.log_le_iff_le_exp hDelpos] at this
    exact this
  have hc2 : C * k * m ^ 4 + r * m ^ 10 < Real.sqrt (bx x eps) := by
    rw [Real.lt_sqrt hSpos.le]
    have e1 : (C * k * m ^ 4 + r * m ^ 10) ^ 2 < (4 * Real.exp t) ^ 2 := by
      have : C * k * m ^ 4 + r * m ^ 10 < 4 * Real.exp t := by linarith
      gcongr
    have e2 : (4 * Real.exp t) ^ 2 = Real.exp (Real.log 16 + 2 * t) := by
      rw [Real.exp_add, Real.exp_log (by norm_num)]
      rw [show 2 * t = t + t by ring, Real.exp_add]; ring
    have e3 : Real.log 16 + 2 * t ≤ x ^ eps := by
      have : Real.log 16 ≤ 16 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      rw [hxe]; nlinarith
    have e4 : Real.exp (Real.log 16 + 2 * t) ≤ bx x eps := by
      unfold bx; exact Real.exp_le_exp.mpr e3
    linarith

  have hc3 : C * k * m ^ 4 + r * m ^ 10 < x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
    have hf35 : f ^ 3 ≤ f ^ 5 := pow_le_pow_right₀ hf1 (by norm_num)
    have e1 : C * k * m ^ 4 + r * m ^ 10 ≤ (C + 2) * r * f ^ 5 := by
      have : (C + 2) * k * f ^ 3 ≤ (C + 2) * r * f ^ 5 := by gcongr
      linarith
    have hx18 : x ≤ x ^ 18 := by
      have := pow_le_pow_right₀ hx1 (show 1 ≤ 18 by norm_num); simpa using this
    have hr18 : x ^ 18 ≤ r ^ 18 := by gcongr
    have e2 : (C + 2) * r * f ^ 5 < r ^ 18 * (r * f ^ 5) := by
      have hp : 0 < r * f ^ 5 := by positivity
      have hC18 : C + 2 < r ^ 18 := by
        have hx2 : x ^ 2 ≤ x ^ 18 := pow_le_pow_right₀ hx1 (by norm_num)
        have : x < x ^ 2 := by nlinarith
        linarith
      have := mul_lt_mul_of_pos_right hC18 hp
      calc (C + 2) * r * f ^ 5 = (C + 2) * (r * f ^ 5) := by ring
        _ < r ^ 18 * (r * f ^ 5) := this
    have e3 : r ^ 18 * (r * f ^ 5) = r ^ 19 * f ^ 5 := by ring
    have e4 : r ^ 19 * f ^ 5 ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
      have hp : 0 ≤ r ^ 19 * f ^ 5 := by positivity
      have h1 : 1 ≤ x ^ (eps / 100) * x ^ eps := one_le_mul_of_one_le_of_one_le hL' hL
      have := mul_le_mul_of_nonneg_right h1 hp
      calc r ^ 19 * f ^ 5 = 1 * (r ^ 19 * f ^ 5) := by ring
        _ ≤ (x ^ (eps / 100) * x ^ eps) * (r ^ 19 * f ^ 5) := this
        _ = x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by ring
    linarith

  have hc4 : C * r ^ 19 * f ^ 5 * x ^ eps ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
    have hCx : C ≤ x ^ (eps / 100) := by
      have h1 : (C ^ (100 / eps)) ^ (eps / 100) ≤ x ^ (eps / 100) :=
        Real.rpow_le_rpow (by positivity) hxC' (by positivity)
      have h2 : (C ^ (100 / eps)) ^ (eps / 100) = C := by
        rw [← Real.rpow_mul hC.le]
        have : 100 / eps * (eps / 100) = 1 := by field_simp
        rw [this, Real.rpow_one]
      linarith
    have hp : 0 ≤ r ^ 19 * f ^ 5 * x ^ eps := by positivity
    have := mul_le_mul_of_nonneg_right hCx hp
    calc C * r ^ 19 * f ^ 5 * x ^ eps = C * (r ^ 19 * f ^ 5 * x ^ eps) := by ring
      _ ≤ x ^ (eps / 100) * (r ^ 19 * f ^ 5 * x ^ eps) := this
      _ = x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by ring
  exact ⟨hc1, hc2, hc3, hc4⟩

end GlobalTheory.Diag.PG
