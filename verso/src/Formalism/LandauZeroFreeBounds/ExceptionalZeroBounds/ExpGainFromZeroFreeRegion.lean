import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ChebyshevCharacterExplicitGeneral
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormIntegralComplLe

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Establish `hT0 : 0 < T` using `by linarith`. Establish `hX0 : 0 < X` using `by nlinarith`. Establish `hX1 : X ≤ 1` using `by nlinarith`. Establish `e1 : ∀ z : ℝ, z / T = z * X` using `fun z => by`. Rewrite using `[div_eq_iff hT0.ne', mul_assoc, mul_comm X T, hTX, mul_one]`.

Establish `e2 : ∀ z : ℝ, z / T ^ 2 = z * X * X` using `fun z => by`. Rewrite using `[div_eq_iff (pow_pos hT0 2).ne']`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [e1, e2]`. Establish `hPw : 0 ≤ Pw` using `by linarith`.

Establish `hyX : 0 ≤ y * X` using `mul_nonneg hy0.le hX0.le`. Establish `hTY : 0 ≤ T * Y` using `mul_nonneg hT0.le hY`. Establish `hcC : 0 ≤ C / c₁` using `div_nonneg hC hc₁.le`. Establish `hc2 : 0 ≤ 24 / c₁ ^ 2` using `by positivity`. Establish `h8 : 0 ≤ 8 / c₁` using `div_nonneg (by norm_num) hc₁.le`.

Establish `k1 : 0 ≤ 2 * Real.pi * Real.exp 1 * (1 + C₀)` using `mul_nonneg (by positivity) (by linarith)`. Establish `k2 : 0 ≤ 6 * Real.exp 1 * (C + 1)` using `mul_nonneg (by positivity) (by linarith)`. Establish `k3 : 0 ≤ 16 * (C / c₁ + 24 / c₁ ^ 2)` using `mul_nonneg (by norm_num) (add_nonneg hcC hc2)`. Establish `h1 : 2 * Real.pi * ((ℓ + C₀) * (Real.exp 1 * y)) * X ≤ 2 * Real.pi * Real.exp 1 * (1 + C₀) * Pw * (y * X)`. Establish `hA : ℓ + C₀ ≤ (1 + C₀) * Pw` using `by nlinarith`.

Establish `hk : 0 ≤ 2 * Real.pi * Real.exp 1 * (y * X)` using `mul_nonneg (by positivity) hyX`. Use `mul_le_mul_of_nonneg_left hA hk` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB0 : 0 ≤ C * L ^ 2 + 1` using `add_nonneg (mul_nonneg hC (sq_nonneg L)) zero_le_one`. Establish `hB : C * L ^ 2 + 1 ≤ (C + 1) * Pw`.

Combine the linear relations using `[mul_le_mul_of_nonneg_left hL2P hC]`. Establish `hXX : X * X ≤ X` using `mul_le_of_le_one_right hX0.le hX1`. Establish `h2 : (C * L ^ 2 + 1) * (Real.exp 1 * y) * X * X * 3 ≤ 3 * Real.exp 1 * (C + 1) * Pw * (y * X)`. Establish `s1 : (C * L ^ 2 + 1) * (X * X) ≤ (C * L ^ 2 + 1) * X` using `mul_le_mul_of_nonneg_left hXX hB0`. Establish `s2 : (C * L ^ 2 + 1) * X ≤ (C + 1) * Pw * X` using `mul_le_mul_of_nonneg_right hB hX0.le`.

Establish `s3` using `mul_le_mul_of_nonneg_left (s1.trans s2) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (mul_nonneg (Real.exp_pos 1).le hy0.le))`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : (C * L ^ 2 + 24 * L / c₁) * Y * (8 * L / c₁) * (2 * T) ≤ 16 * (C / c₁ + 24 / c₁ ^ 2) * Pw * (T * Y)`. Establish `hid : (C * L ^ 2 + 24 * L / c₁) * Y * (8 * L / c₁) * (2 * T) = (16 * (C / c₁) * L ^ 3 + 16 * (24 / c₁ ^ 2) * L ^ 2) * (T * Y)` using `by ring`. Rewrite using `[hid]`.

Apply `mul_le_mul_of_nonneg_right _ hTY` to reduce the goal to its premises. Combine the linear relations using `[mul_le_mul_of_nonneg_left hL3P hcC, mul_le_mul_of_nonneg_left hL2P hc2]`. Establish `h4 : Y * (8 * L / c₁) ≤ 8 / c₁ * Pw * (T * Y)`. Establish `hid : Y * (8 * L / c₁) = 8 / c₁ * L * Y` using `by ring`. Rewrite using `[hid]`.

Establish `s1 : 8 / c₁ * L ≤ 8 / c₁ * Pw` using `mul_le_mul_of_nonneg_left hLP h8`. Establish `s2 : Y ≤ T * Y` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg k1 hPw) hTY, mul_nonneg (mul_nonneg k2 hPw) hTY, mul_nonneg (mul_nonneg k3 hPw) hyX, mul_nonneg (mul_nonneg h8 hPw) hyX]`.
-/
theorem perron_error_terms_sum_bound (C C₀ c₁ y T X L Pw Y ℓ : ℝ) (hc₁ : 0 < c₁) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hy0 : 0 < y) (hT1 : 1 ≤ T) (hTX : T * X = 1) (hL0 : 0 ≤ L) (hY : 0 ≤ Y)
    (hℓP : ℓ ≤ Pw) (hP1 : 1 ≤ Pw) (hL2P : L ^ 2 ≤ Pw) (hL3P : L ^ 3 ≤ Pw) (hLP : L ≤ Pw) :
    2 * Real.pi * ((ℓ + C₀) * (Real.exp 1 * y)) / T
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 24 * L / c₁) * Y * (8 * L / c₁) * (2 * T)
        + Y * (8 * L / c₁) ≤
      (2 * Real.pi * Real.exp 1 * (1 + C₀) + 6 * Real.exp 1 * (C + 1) +
        16 * (C / c₁ + 24 / c₁ ^ 2) + 8 / c₁) * Pw * (y * X + T * Y) := by
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by nlinarith
  have hX1 : X ≤ 1 := by nlinarith
  have e1 : ∀ z : ℝ, z / T = z * X := fun z => by
    rw [div_eq_iff hT0.ne', mul_assoc, mul_comm X T, hTX, mul_one]
  have e2 : ∀ z : ℝ, z / T ^ 2 = z * X * X := fun z => by
    rw [div_eq_iff (pow_pos hT0 2).ne']
    calc z = z * (T * X) * (T * X) := by rw [hTX]; ring
      _ = z * X * X * T ^ 2 := by ring
  simp only [e1, e2]
  have hPw : 0 ≤ Pw := by linarith
  have hyX : 0 ≤ y * X := mul_nonneg hy0.le hX0.le
  have hTY : 0 ≤ T * Y := mul_nonneg hT0.le hY
  have hcC : 0 ≤ C / c₁ := div_nonneg hC hc₁.le
  have hc2 : 0 ≤ 24 / c₁ ^ 2 := by positivity
  have h8 : 0 ≤ 8 / c₁ := div_nonneg (by norm_num) hc₁.le
  have k1 : 0 ≤ 2 * Real.pi * Real.exp 1 * (1 + C₀) := mul_nonneg (by positivity) (by linarith)
  have k2 : 0 ≤ 6 * Real.exp 1 * (C + 1) := mul_nonneg (by positivity) (by linarith)
  have k3 : 0 ≤ 16 * (C / c₁ + 24 / c₁ ^ 2) := mul_nonneg (by norm_num) (add_nonneg hcC hc2)
  have h1 : 2 * Real.pi * ((ℓ + C₀) * (Real.exp 1 * y)) * X ≤
      2 * Real.pi * Real.exp 1 * (1 + C₀) * Pw * (y * X) := by
    have hA : ℓ + C₀ ≤ (1 + C₀) * Pw := by nlinarith
    have hk : 0 ≤ 2 * Real.pi * Real.exp 1 * (y * X) := mul_nonneg (by positivity) hyX
    have := mul_le_mul_of_nonneg_left hA hk
    linarith
  have hB0 : 0 ≤ C * L ^ 2 + 1 := add_nonneg (mul_nonneg hC (sq_nonneg L)) zero_le_one
  have hB : C * L ^ 2 + 1 ≤ (C + 1) * Pw := by
    linarith [mul_le_mul_of_nonneg_left hL2P hC]
  have hXX : X * X ≤ X := mul_le_of_le_one_right hX0.le hX1
  have h2 : (C * L ^ 2 + 1) * (Real.exp 1 * y) * X * X * 3 ≤ 3 * Real.exp 1 * (C + 1) * Pw * (y * X) := by
    have s1 : (C * L ^ 2 + 1) * (X * X) ≤ (C * L ^ 2 + 1) * X := mul_le_mul_of_nonneg_left hXX hB0
    have s2 : (C * L ^ 2 + 1) * X ≤ (C + 1) * Pw * X := mul_le_mul_of_nonneg_right hB hX0.le
    have s3 := mul_le_mul_of_nonneg_left (s1.trans s2)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (mul_nonneg (Real.exp_pos 1).le hy0.le))
    linarith
  have h3 : (C * L ^ 2 + 24 * L / c₁) * Y * (8 * L / c₁) * (2 * T) ≤
      16 * (C / c₁ + 24 / c₁ ^ 2) * Pw * (T * Y) := by
    have hid : (C * L ^ 2 + 24 * L / c₁) * Y * (8 * L / c₁) * (2 * T) =
        (16 * (C / c₁) * L ^ 3 + 16 * (24 / c₁ ^ 2) * L ^ 2) * (T * Y) := by ring
    rw [hid]
    apply mul_le_mul_of_nonneg_right _ hTY
    linarith [mul_le_mul_of_nonneg_left hL3P hcC, mul_le_mul_of_nonneg_left hL2P hc2]
  have h4 : Y * (8 * L / c₁) ≤ 8 / c₁ * Pw * (T * Y) := by
    have hid : Y * (8 * L / c₁) = 8 / c₁ * L * Y := by ring
    rw [hid]
    have s1 : 8 / c₁ * L ≤ 8 / c₁ * Pw := mul_le_mul_of_nonneg_left hLP h8
    have s2 : Y ≤ T * Y := by nlinarith
    calc 8 / c₁ * L * Y ≤ 8 / c₁ * Pw * Y := mul_le_mul_of_nonneg_right s1 hY
      _ ≤ 8 / c₁ * Pw * (T * Y) := mul_le_mul_of_nonneg_left s2 (mul_nonneg h8 hPw)
  nlinarith [mul_nonneg (mul_nonneg k1 hPw) hTY, mul_nonneg (mul_nonneg k2 hPw) hTY,
    mul_nonneg (mul_nonneg k3 hPw) hyX, mul_nonneg (mul_nonneg h8 hPw) hyX]

/- English proof (translation)
Establish `hy : y = Real.exp (s ^ 2)` using `by rw [← hℓ, Real.exp_log hy0]`. Establish `hyσ : y ^ σ₁ = Real.exp (s ^ 2 * σ₁)` using `by rw [Real.rpow_def_of_pos hy0, hℓ]`. Rewrite using `[hyσ, ← Real.exp_add, hy, ← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `h4L : 0 < 4 * L` using `by linarith`.

Establish `hq : c₁ ≤ c₁ / (4 * L) * s`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ h4L]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hc : c₁ ≤ (1 - σ₁) * s`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right (by linarith : c₁ / (4 * L) ≤ 1 - σ₁) hs0.le]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hc hs0.le]`.
-/
theorem exp_gain_from_zero_free_region (y s c₁ σ₁ L : ℝ) (hy0 : 0 < y) (hℓ : Real.log y = s ^ 2) (hs0 : 0 < s)
    (hc₁ : 0 < c₁) (hL : 0 < L) (hL4 : 4 * L ≤ s) (hσ : σ₁ ≤ 1 - c₁ / (4 * L)) :
    Real.exp (c₁ * s / 2) * y ^ σ₁ ≤ y * Real.exp (-(c₁ * s / 2)) := by
  have hy : y = Real.exp (s ^ 2) := by rw [← hℓ, Real.exp_log hy0]
  have hyσ : y ^ σ₁ = Real.exp (s ^ 2 * σ₁) := by rw [Real.rpow_def_of_pos hy0, hℓ]
  rw [hyσ, ← Real.exp_add, hy, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h4L : 0 < 4 * L := by linarith
  have hq : c₁ ≤ c₁ / (4 * L) * s := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h4L]; nlinarith
  have hc : c₁ ≤ (1 - σ₁) * s := by
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : c₁ / (4 * L) ≤ 1 - σ₁) hs0.le]
  nlinarith [mul_le_mul_of_nonneg_right hc hs0.le]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `h : c₁ * s / 2 ≤ 1` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Establish `h : -(1 / 8 : ℝ) ≤ -(c₁ / 4) * s` using `by nlinarith`. Use `Real.add_one_le_exp (-(c₁ / 4) * s)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem small_scale_exp_bounds (c₁ s : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 20) (hs : s < 10) :
    Real.exp (c₁ * s / 2) ≤ 3 ∧ 1 ≤ 3 * Real.exp (-(c₁ / 4) * s) := by
  constructor
  · have h : c₁ * s / 2 ≤ 1 := by nlinarith
    calc Real.exp (c₁ * s / 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr h
      _ ≤ 3 := by have := Real.exp_one_lt_d9; norm_num at this; linarith
  · have h : -(1 / 8 : ℝ) ≤ -(c₁ / 4) * s := by nlinarith
    have := Real.add_one_le_exp (-(c₁ / 4) * s)
    linarith

/- English proof (translation)
Establish `hu0 : 0 < c₁ * s / 4` using `div_pos (mul_pos hc₁ hs0) (by norm_num)`. Establish `hexp : (c₁ * s / 4) ^ 3 / 6 ≤ Real.exp (c₁ * s / 4)`. Establish `h` using `Real.pow_div_factorial_le_exp (c₁ * s / 4) hu0.le 3`. Evaluate the numerical expressions using `[Nat.factorial] at h`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hX' : X = Real.exp (-(c₁ * s / 4)) * Real.exp (-(c₁ * s / 4))`. Rewrite using `[hX, ← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `he : Real.exp (-(c₁ / 4) * s) = Real.exp (-(c₁ * s / 4))` using `by congr 1; ring`.

Rewrite using `[he, hX']`. Establish `hu3 : (c₁ * s / 4) ^ 3 * Real.exp (-(c₁ * s / 4)) ≤ 6`. Establish `h2 : Real.exp (c₁ * s / 4) * Real.exp (-(c₁ * s / 4)) = 1`. Rewrite using `[← Real.exp_add]`. Simplify using the standard rewrite rules.

Establish `h3` using `mul_le_mul_of_nonneg_right (by linarith : (c₁ * s / 4) ^ 3 ≤ 6 * Real.exp (c₁ * s / 4)) (Real.exp_pos (-(c₁ * s / 4))).le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsu : s = 8 / (2 * c₁) * (c₁ * s / 4)`. Use `hc₁.ne'` as an intermediate fact. Clear the denominators using the available nonvanishing facts.

Apply the tactic sequence `try ring`. Establish `hK : 0 ≤ (8 / (2 * c₁)) ^ 3` using `pow_nonneg (div_nonneg (by norm_num) (by linarith)) 3`. Establish `key : s ^ 3 * Real.exp (-(c₁ * s / 4)) ≤ 6 * (8 / (2 * c₁)) ^ 3`. Establish `hs3 : s ^ 3 = (8 / (2 * c₁)) ^ 3 * (c₁ * s / 4) ^ 3`. Rewrite using `[← mul_pow, ← hsu]`.

Rewrite using `[hs3]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hu3 hK]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right key (mul_pos (Real.exp_pos (-(c₁ * s / 4))) hy0).le]`.
-/
theorem cube_mul_exp_le_poly_bound (c₁ s y X : ℝ) (hc₁ : 0 < c₁) (hs0 : 0 < s) (hy0 : 0 < y)
    (hX : X = Real.exp (-(c₁ * s / 2))) :
    s ^ 3 * X * y ≤ 6 * (8 / (2 * c₁)) ^ 3 * (y * Real.exp (-(c₁ / 4) * s)) := by
  have hu0 : 0 < c₁ * s / 4 := div_pos (mul_pos hc₁ hs0) (by norm_num)
  have hexp : (c₁ * s / 4) ^ 3 / 6 ≤ Real.exp (c₁ * s / 4) := by
    have h := Real.pow_div_factorial_le_exp (c₁ * s / 4) hu0.le 3
    norm_num [Nat.factorial] at h
    linarith
  have hX' : X = Real.exp (-(c₁ * s / 4)) * Real.exp (-(c₁ * s / 4)) := by
    rw [hX, ← Real.exp_add]; congr 1; ring
  have he : Real.exp (-(c₁ / 4) * s) = Real.exp (-(c₁ * s / 4)) := by congr 1; ring
  rw [he, hX']
  have hu3 : (c₁ * s / 4) ^ 3 * Real.exp (-(c₁ * s / 4)) ≤ 6 := by
    have h2 : Real.exp (c₁ * s / 4) * Real.exp (-(c₁ * s / 4)) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 := mul_le_mul_of_nonneg_right (by linarith : (c₁ * s / 4) ^ 3 ≤ 6 * Real.exp (c₁ * s / 4))
      (Real.exp_pos (-(c₁ * s / 4))).le
    linarith
  have hsu : s = 8 / (2 * c₁) * (c₁ * s / 4) := by
    have := hc₁.ne'
    field_simp
    try ring
  have hK : 0 ≤ (8 / (2 * c₁)) ^ 3 := pow_nonneg (div_nonneg (by norm_num) (by linarith)) 3
  have key : s ^ 3 * Real.exp (-(c₁ * s / 4)) ≤ 6 * (8 / (2 * c₁)) ^ 3 := by
    have hs3 : s ^ 3 = (8 / (2 * c₁)) ^ 3 * (c₁ * s / 4) ^ 3 := by
      rw [← mul_pow, ← hsu]
    rw [hs3]
    nlinarith [mul_le_mul_of_nonneg_left hu3 hK]
  nlinarith [mul_le_mul_of_nonneg_right key (mul_pos (Real.exp_pos (-(c₁ * s / 4))) hy0).le]

end Formalism.ZeroFreeDirichlet
