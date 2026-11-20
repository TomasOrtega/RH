import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty

open GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG

/- English proof (translation)
Introduce `eps CD heps _ _ C hC`. Use `set M : ℝ := max C 3 with hMdef`. Establish `hM3 : 3 ≤ M` using `le_max_right _ _`. Establish `hMC : C ≤ M` using `le_max_left _ _`. Establish `hM0 : 0 ≤ M` using `by linarith`.

Use `⟨max (max 1 C) (M ^ (2 / eps)), ?_⟩` and prove the remaining obligations. Introduce `x hx m f k lrd Del h`. Establish `hx1 : 1 ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `hxC : C ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`. Establish `hxM : M ^ (2 / eps) ≤ x` using `le_trans (le_max_right _ _) hx`.

Establish `hx0 : 0 < x` using `by linarith`. Use `set X : ℝ := x ^ (eps / 2) with hXdef`. Establish `hXM : M ≤ X`. Establish `h1 : (M ^ (2 / eps)) ^ (eps / 2) ≤ x ^ (eps / 2)` using `Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) hxM (by linarith)`. Rewrite `h1` using `[← Real.rpow_mul hM0]`.

Establish `h2 : 2 / eps * (eps / 2) = 1` using `by field_simp`. Rewrite `h1` using `[h2, Real.rpow_one]`. Conclude with `h1`. Establish `hYX : x ^ eps = X * X`. Rewrite using `[hXdef, ← Real.rpow_add hx0]`.

Put the polynomial expressions in normal form. Establish `hX3 : 3 ≤ X` using `le_trans hM3 hXM`. Establish `hXC : C ≤ X` using `le_trans hMC hXM`. Establish `hm1 : 1 ≤ m` using `le_trans (Real.one_le_rpow hx1 (by norm_num)) h.m_lo`. Establish `hm4 : x ≤ m ^ 4`.

Establish `h1 : (x ^ ((1 : ℝ) / 4)) ^ 4 = x`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hx0.le]`. Evaluate the numerical expressions. Combine the equalities or inequalities in the displayed calculation. Establish `hf : x ≤ f` using `le_trans hm4 h.mf`.

Establish `hf1 : 1 ≤ f` using `le_trans hx1 hf`. Establish `hm0 : 0 ≤ m` using `by linarith`. Establish `hm2 : 1 ≤ m ^ 2` using `one_le_pow₀ hm1`. Establish `hm3 : 1 ≤ m ^ 3` using `one_le_pow₀ hm1`. Establish `hm4' : 1 ≤ m ^ 4` using `one_le_pow₀ hm1`.

Establish `hk : X * (m ^ 5 * f * (X * X)) ≤ k`. Use `h.k_lo` as an intermediate fact. Rewrite `this` using `[hYX]`. Conclude with `this`. Establish `hlrd : lrd ≤ X` using `h.lrd_hi`.

Establish `hlog2 : 0 ≤ Real.log 2` using `Real.log_nonneg (by norm_num)`. Establish `hlrd0 : 0 ≤ lrd` using `le_trans hlog2 h.lrd_lo`. Establish `hX0 : 0 ≤ X` using `by linarith`. Establish `hXX : X ≤ X * X` using `by nlinarith`. Establish `hA : C ≤ m ^ 4 * f * (X * X)`.

Establish `h1 : 1 ≤ m ^ 4 * f` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Establish `hB : C ≤ m ^ 2 * f`. Combine the equalities or inequalities in the displayed calculation. Establish `hkX : X ≤ k`.

Establish `h1 : 1 ≤ m ^ 5 * f * (X * X)`. Establish `: 1 ≤ m ^ 5` using `one_le_pow₀ hm1`. Establish `: 1 ≤ X * X` using `by nlinarith`. Establish `: 1 ≤ m ^ 5 * f` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Use the polynomial consequences of the given equalities and inequalities. Establish `hk0 : 0 < k` using `by linarith`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left _ hC.le` to reduce the goal to its premises.

Apply `mul_le_mul_of_nonneg_left _ hm0` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = (m * X) * C := by ring`. Use `_ ≤ (m * X) * (m ^ 4 * f * (X * X)) := mul_le_mul_of_nonneg_left hA (by positivity)`. Use `_ = X * (m ^ 5 * f * (X * X)) := by ring`.

Use `_ ≤ k := hk`. Establish `hlogk : 1 ≤ Real.log k`. Rewrite using `[Real.le_log_iff_exp_le hk0]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hl2 : 1 ≤ Real.log k ^ 2` using `one_le_pow₀ hlogk`. Rewrite using `[hYX]`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left _ hC.le` to reduce the goal to its premises. Apply `mul_le_mul_of_nonneg_left hlrd (by positivity)` to reduce the goal to its premises.

Use `_ = (m ^ 3 * (X * X) * X) * C := by ring`. Use `_ ≤ (m ^ 3 * (X * X) * X) * (m ^ 2 * f) := mul_le_mul_of_nonneg_left hB (by positivity)`. Use `_ = X * (m ^ 5 * f * (X * X)) := by ring`. Use `_ ≤ k := hk`. Use `_ = k * 1 := by ring`.

Use `_ ≤ k * Real.log k ^ 2 := mul_le_mul_of_nonneg_left hl2 hk0.le`. Rewrite using `[hYX, le_div_iff₀ hC]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rankNums_rootDisc :
    ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x →
      ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del →
        C * (m * (lrd - Real.log 2)) ≤ k ∧ C * (m ^ 3 * x ^ eps * lrd) ≤ k * Real.log k ^ 2 ∧
          lrd ≤ x ^ eps / C := by
  intro eps CD heps _ _ C hC
  set M : ℝ := max C 3 with hMdef
  have hM3 : 3 ≤ M := le_max_right _ _
  have hMC : C ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := by linarith
  refine ⟨max (max 1 C) (M ^ (2 / eps)), ?_⟩
  intro x hx m f k lrd Del h
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxC : C ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxM : M ^ (2 / eps) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  set X : ℝ := x ^ (eps / 2) with hXdef
  have hXM : M ≤ X := by
    have h1 : (M ^ (2 / eps)) ^ (eps / 2) ≤ x ^ (eps / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) hxM (by linarith)
    rw [← Real.rpow_mul hM0] at h1
    have h2 : 2 / eps * (eps / 2) = 1 := by field_simp
    rw [h2, Real.rpow_one] at h1
    exact h1
  have hYX : x ^ eps = X * X := by
    rw [hXdef, ← Real.rpow_add hx0]; ring_nf
  have hX3 : 3 ≤ X := le_trans hM3 hXM
  have hXC : C ≤ X := le_trans hMC hXM
  have hm1 : 1 ≤ m := le_trans (Real.one_le_rpow hx1 (by norm_num)) h.m_lo
  have hm4 : x ≤ m ^ 4 := by
    have h1 : (x ^ ((1 : ℝ) / 4)) ^ 4 = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    calc x = (x ^ ((1 : ℝ) / 4)) ^ 4 := h1.symm
      _ ≤ m ^ 4 := pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) h.m_lo 4
  have hf : x ≤ f := le_trans hm4 h.mf
  have hf1 : 1 ≤ f := le_trans hx1 hf
  have hm0 : 0 ≤ m := by linarith
  have hm2 : 1 ≤ m ^ 2 := one_le_pow₀ hm1
  have hm3 : 1 ≤ m ^ 3 := one_le_pow₀ hm1
  have hm4' : 1 ≤ m ^ 4 := one_le_pow₀ hm1
  have hk : X * (m ^ 5 * f * (X * X)) ≤ k := by
    have := h.k_lo; rw [hYX] at this; exact this
  have hlrd : lrd ≤ X := h.lrd_hi
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlrd0 : 0 ≤ lrd := le_trans hlog2 h.lrd_lo
  have hX0 : 0 ≤ X := by linarith
  have hXX : X ≤ X * X := by nlinarith

  have hA : C ≤ m ^ 4 * f * (X * X) := by
    have h1 : 1 ≤ m ^ 4 * f := by nlinarith
    calc C ≤ X * X := le_trans hXC hXX
      _ = 1 * (X * X) := by ring
      _ ≤ m ^ 4 * f * (X * X) := mul_le_mul_of_nonneg_right h1 (by positivity)

  have hB : C ≤ m ^ 2 * f := by
    calc C ≤ x := hxC
      _ ≤ f := hf
      _ = 1 * f := by ring
      _ ≤ m ^ 2 * f := mul_le_mul_of_nonneg_right hm2 (by linarith)
  have hkX : X ≤ k := by
    have h1 : 1 ≤ m ^ 5 * f * (X * X) := by
      have : 1 ≤ m ^ 5 := one_le_pow₀ hm1
      have : 1 ≤ X * X := by nlinarith
      have : 1 ≤ m ^ 5 * f := by nlinarith
      nlinarith
    nlinarith
  have hk0 : 0 < k := by linarith
  refine ⟨?_, ?_, ?_⟩
  · calc C * (m * (lrd - Real.log 2)) ≤ C * (m * X) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          apply mul_le_mul_of_nonneg_left _ hm0
          linarith
      _ = (m * X) * C := by ring
      _ ≤ (m * X) * (m ^ 4 * f * (X * X)) := mul_le_mul_of_nonneg_left hA (by positivity)
      _ = X * (m ^ 5 * f * (X * X)) := by ring
      _ ≤ k := hk
  · have hlogk : 1 ≤ Real.log k := by
      rw [Real.le_log_iff_exp_le hk0]
      have := Real.exp_one_lt_d9
      linarith
    have hl2 : 1 ≤ Real.log k ^ 2 := one_le_pow₀ hlogk
    rw [hYX]
    calc C * (m ^ 3 * (X * X) * lrd) ≤ C * (m ^ 3 * (X * X) * X) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          apply mul_le_mul_of_nonneg_left hlrd (by positivity)
      _ = (m ^ 3 * (X * X) * X) * C := by ring
      _ ≤ (m ^ 3 * (X * X) * X) * (m ^ 2 * f) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = X * (m ^ 5 * f * (X * X)) := by ring
      _ ≤ k := hk
      _ = k * 1 := by ring
      _ ≤ k * Real.log k ^ 2 := mul_le_mul_of_nonneg_left hl2 hk0.le
  · rw [hYX, le_div_iff₀ hC]
    calc lrd * C ≤ X * C := mul_le_mul_of_nonneg_right hlrd hC.le
      _ ≤ X * X := mul_le_mul_of_nonneg_left hXC hX0

end GlobalTheory.Diag.PG
