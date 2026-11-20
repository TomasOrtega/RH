import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

/- English proof (translation)
Apply `ContinuousOn.intervalIntegrable` to reduce the goal to its premises. Use `continuousOn_const.div (Real.continuousOn_log.mono ?_) ?_` and prove the remaining obligations. Introduce `t ht`. Rewrite `ht` using `[Set.uIcc_of_le hY]`. Conclude with `Set.mem_compl_singleton_iff.2 (by linarith [ht.1] : (0 : ℝ) < t).ne'`.

Introduce `t ht`. Rewrite `ht` using `[Set.uIcc_of_le hY]`. Conclude with `(Real.log_pos (by linarith [ht.1])).ne'`.
-/
private lemma intervalIntegrable_inv_log_two {Y : ℝ} (hY : 2 ≤ Y) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume 2 Y := by
  apply ContinuousOn.intervalIntegrable
  refine continuousOn_const.div (Real.continuousOn_log.mono ?_) ?_
  · intro t ht
    rw [Set.uIcc_of_le hY] at ht
    exact Set.mem_compl_singleton_iff.2 (by linarith [ht.1] : (0 : ℝ) < t).ne'
  · intro t ht
    rw [Set.uIcc_of_le hY] at ht
    exact (Real.log_pos (by linarith [ht.1])).ne'

/- English proof (translation)
Establish `hpos : ∀ t ∈ Set.Icc (2 : ℝ) Y, 0 < Real.log t` using `fun t ht => Real.log_pos (by linarith [ht.1])`. Establish `hlog2 : (1 : ℝ) / 2 < Real.log 2` using `by have := Real.log_two_gt_d9; linarith`. Prove the components needed by the constructor for the conclusion. Unfold `liX`. Conclude with `intervalIntegral.integral_nonneg hY (fun t ht => (one_div_pos.2 (hpos t ht)).le)`.

Unfold `liX`. Combine the equalities or inequalities in the displayed calculation. Apply `intervalIntegral.integral_mono_on hY (intervalIntegrable_inv_log_two hY) intervalIntegrable_const` to reduce the goal to its premises. Introduce `t ht`. Establish `h1 : Real.log 2 ≤ Real.log t` using `Real.log_le_log (by norm_num) ht.1`.

Rewrite using `[div_le_iff₀ (hpos t ht)]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = (Y - 2) * 2 := by simp`. Use `_ ≤ 2 * Y := by linarith`.
-/
theorem liX_upper {Y : ℝ} (hY : 2 ≤ Y) : 0 ≤ liX Y ∧ liX Y ≤ 2 * Y := by
  have hpos : ∀ t ∈ Set.Icc (2 : ℝ) Y, 0 < Real.log t := fun t ht => Real.log_pos (by linarith [ht.1])
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  constructor
  · unfold liX
    exact intervalIntegral.integral_nonneg hY (fun t ht => (one_div_pos.2 (hpos t ht)).le)
  · unfold liX
    calc ∫ t in (2 : ℝ)..Y, 1 / Real.log t ≤ ∫ t in (2 : ℝ)..Y, (2 : ℝ) := by
          apply intervalIntegral.integral_mono_on hY (intervalIntegrable_inv_log_two hY) intervalIntegrable_const
          intro t ht
          have h1 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.1
          rw [div_le_iff₀ (hpos t ht)]
          linarith
      _ = (Y - 2) * 2 := by simp
      _ ≤ 2 * Y := by linarith

/- English proof (translation)
Establish `hX2 : (2 : ℝ) ≤ X` using `by linarith`. Establish `hLX : 0 < Real.log X` using `Real.log_pos (by linarith)`. Establish `hmono : ∫ t in (2 : ℝ)..X, 1 / Real.log X ≤ liX X`. Unfold `liX`. Apply `intervalIntegral.integral_mono_on hX2 intervalIntegrable_const (intervalIntegrable_inv_log_two hX2)` to reduce the goal to its premises.

Introduce `t ht`. Establish `ht0 : 0 < Real.log t` using `Real.log_pos (by linarith [ht.1])`. Conclude with `one_div_le_one_div_of_le ht0 (Real.log_le_log (by linarith [ht.1]) ht.2)`. Rewrite `hmono` using `[intervalIntegral.integral_const, smul_eq_mul]`. Use `le_trans ?_ hmono` and prove the remaining obligations.

Rewrite using `[mul_one_div, div_le_div_iff₀ (by linarith) hLX]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hX hLX.le]`.
-/
theorem liX_lower {X : ℝ} (hX : 4 ≤ X) : X / (2 * Real.log X) ≤ liX X := by
  have hX2 : (2 : ℝ) ≤ X := by linarith
  have hLX : 0 < Real.log X := Real.log_pos (by linarith)
  have hmono : ∫ t in (2 : ℝ)..X, 1 / Real.log X ≤ liX X := by
    unfold liX
    apply intervalIntegral.integral_mono_on hX2 intervalIntegrable_const (intervalIntegrable_inv_log_two hX2)
    intro t ht
    have ht0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    exact one_div_le_one_div_of_le ht0 (Real.log_le_log (by linarith [ht.1]) ht.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  refine le_trans ?_ hmono
  rw [mul_one_div, div_le_div_iff₀ (by linarith) hLX]
  nlinarith [mul_le_mul_of_nonneg_right hX hLX.le]

/- English proof (translation)
The claim follows from `|liX (X ^ β)| ≤ 4 * Real.log X * Real.exp (-(δ * Real.log X)) * liX X := by obtain ⟨L, hL⟩ : ∃ L, L = Real.log X := ⟨_, rfl⟩ rw [← hL] have hXpos : 0 < X := by linarith have hL0 : 0 < L := by rw [hL]; exact Real.log_pos (by linarith) have hXL : X = Real.exp L := by rw [hL, Real.e …`.
-/
theorem liX_pow_le {X β δ : ℝ} (hX : 4 ≤ X) (hβ1 : 1 / 2 ≤ β) (hβ2 : β ≤ 1 - δ) :
    |liX (X ^ β)| ≤ 4 * Real.log X * Real.exp (-(δ * Real.log X)) * liX X := by
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log X := ⟨_, rfl⟩
  rw [← hL]
  have hXpos : 0 < X := by linarith
  have hL0 : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  have hXL : X = Real.exp L := by rw [hL, Real.exp_log hXpos]
  have hXb2 : 2 ≤ X ^ β := by
    have h4 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc (2 : ℝ) = 4 ^ ((1 : ℝ) / 2) := h4.symm
      _ ≤ X ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by norm_num) hX (by norm_num)
      _ ≤ X ^ β := Real.rpow_le_rpow_of_exponent_le (by linarith) hβ1
  obtain ⟨h0, hup⟩ := liX_upper hXb2
  have hlow : X / (2 * L) ≤ liX X := by rw [hL]; exact liX_lower hX
  calc |liX (X ^ β)| = liX (X ^ β) := abs_of_nonneg h0
    _ ≤ 2 * X ^ β := hup
    _ = 2 * Real.exp (β * L) := by rw [Real.rpow_def_of_pos hXpos, ← hL, mul_comm L β]
    _ ≤ 2 * Real.exp ((1 - δ) * L) := by
        have : β * L ≤ (1 - δ) * L := mul_le_mul_of_nonneg_right hβ2 hL0.le
        have := Real.exp_le_exp.2 this
        linarith
    _ = 4 * L * Real.exp (-(δ * L)) * (X / (2 * L)) := by
        rw [hXL, show (1 - δ) * L = -(δ * L) + L by ring, Real.exp_add]
        field_simp
        ring
    _ ≤ 4 * L * Real.exp (-(δ * L)) * liX X :=
        mul_le_mul_of_nonneg_left hlow (by positivity)

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `hL0 : 0 < L` using `by linarith`. Establish `hL1' : 1 ≤ L` using `by linarith`. Establish `hc3L3 : 0 ≤ 16 / c₃ * L ^ 3` using `by positivity`. Establish `hu200 : 200 * L ^ 3 ≤ u` using `by nlinarith [hu2]`. Establish `hu0 : 0 < u` using `by nlinarith [pow_pos hL0 3]`.

Establish `hkey : L ^ 2 * (ℓm + 800 * L) / 8 ≤ u` using `by nlinarith [hu1, hu2]`. Establish `hℓ0 : 0 < ℓ` using `by linarith`. Establish `hlm0' : 0 < lm` using `by linarith`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hlog_pos : 0 < Real.log (lm + 2)` using `Real.log_pos (by linarith)`.

Break down `le_or_gt C₀ 0 with hC | hC` into its components or cases. Establish `: C₀ * lm * Real.log (lm + 2) ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hC hlm0'.le) hlog_pos.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hexp1 : 1 ≤ Real.exp (ε / 5 * L)` using `Real.one_le_exp (by positivity)`. Establish `hlm2 : lm + 2 ≤ 806 * L * Real.exp (ε / 5 * L)`.

Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 hexp1) (by linarith : (0 : ℝ) ≤ 806 * L - 4)]`. Establish `hloglm : Real.log (lm + 2) ≤ Real.log 806 + Real.log L + ε / 5 * L`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity), Real.log_exp]`. Establish `hlogL : Real.log L ≤ L` using `(Real.log_le_sub_one_of_pos hL0).trans (by linarith)`.

Establish `h806 : 0 ≤ Real.log 806` using `Real.log_nonneg (by norm_num)`. Establish `hlog2 : Real.log (lm + 2) ≤ L * (Real.log 806 + ε / 5 + 1)`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 hL1') h806]`. Rewrite `hL5` using `[abs_of_pos hC]`. Establish `hC' : C₀ * Real.log (lm + 2) ≤ L ^ 2 / 8`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Establish `hlog128 : 0 < Real.log 128` using `Real.log_pos (by norm_num)`. Establish `harg : 3 * L + Real.log 128 + Real.log u ≤ c₀ / ℓ * u`. Establish `h1 : ℓ * L ^ 2 / 8 ≤ u`.

Use polynomial arithmetic with `[hkey, mul_le_mul_of_nonneg_right (show ℓ ≤ ℓm + 800 * L by linarith) (sq_nonneg L)]`. Establish `h2 : c₀ * L ^ 2 / 8 ≤ c₀ / ℓ * u`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ hℓ0]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h1 hc₀.le]`. Establish `h3 : 3 * L + Real.log 128 + Real.log u ≤ c₀ * L ^ 2 / 8`.

Establish `: ε / 5 + 5 + Real.log 128 ≤ c₀ * L / 8`. Rewrite `hL2` using `[div_le_iff₀ hc₀]`. Combine the linear equalities and inequalities to obtain the conclusion. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left this hL0.le, mul_nonneg (sub_nonneg.2 hL1') hlog128.le]`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show -(3 * L + Real.log 128 + Real.log u) = -(3 * L) - Real.log (128 * u) by`. Rewrite using `[Real.log_mul (by norm_num) hu0.ne']; ring,`. Use the proof step `Real.exp_sub, Real.exp_log (by linarith)]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Take `⟨B, hBdef⟩ : ∃ B, B = Real.log (32 * (|A₀| + 1))` from `⟨_, rfl⟩`. Rewrite `hL3`, `hL4` using `[← hBdef]`. Establish `hA1 : 0 < 32 * (|A₀| + 1)` using `by positivity`. Establish `hB0 : 0 < B` using `by rw [hBdef]; exact Real.log_pos (by linarith [abs_nonneg A₀])`.

Establish `hexpB : Real.exp (-(3 * L + B)) = Real.exp (-(3 * L)) / (32 * (|A₀| + 1))`. Rewrite using `[show -(3 * L + B) = -(3 * L) - B by ring, Real.exp_sub, hBdef, Real.exp_log hA1]`. Establish `hc3L : 3 + B ≤ c₃ * L / 8`. Rewrite `hL3` using `[div_le_iff₀ hc₃]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hE1 : Real.exp (-(c₃ * u / lm)) ≤ Real.exp (-(3 * L + B))`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Establish `h1 : lm * L ^ 2 / 8 ≤ u`. Use polynomial arithmetic with `[hkey, mul_le_mul_of_nonneg_right (show lm ≤ ℓm + 800 * L by linarith) (sq_nonneg L)]`. Establish `h2 : c₃ * L ^ 2 / 8 ≤ c₃ * u / lm`.

Rewrite using `[le_div_iff₀ hlm0']`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h1 hc₃.le]`. Establish `h3 : 3 * L + B ≤ c₃ * L ^ 2 / 8`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hc3L hL0.le, mul_nonneg (sub_nonneg.2 hL1') hB0.le]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hE2 : Real.exp (-Real.sqrt (c₃ * u)) ≤ Real.exp (-(3 * L + B))`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Establish `h0 : c₃ * ((200 + 16 / c₃) * L ^ 3) ≤ c₃ * u` using `mul_le_mul_of_nonneg_left hu2 hc₃.le`. Establish `e' : c₃ * ((200 + 16 / c₃) * L ^ 3) = 200 * c₃ * L ^ 3 + 16 * L ^ 3`. Clear the denominators using the available nonvanishing facts.

Rewrite `h0` using `[e']`. Establish `hL23 : L ^ 2 ≤ L ^ 3` using `pow_le_pow_right₀ hL1' (by norm_num)`. Establish `h1 : (4 * L) ^ 2 ≤ c₃ * u` using `by nlinarith [mul_pos hc₃ (pow_pos hL0 3)]`. Establish `h2 : 4 * L ≤ Real.sqrt (c₃ * u)`. Use `Real.sqrt_le_sqrt h1` as an intermediate fact.

Rewrite `this` using `[Real.sqrt_sq (by linarith)]`. Then use the resulting hypothesis. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht1 : 0 < |A₀| + 1` using `by positivity`. Establish `hsum : Real.exp (-(c₃ * u / lm)) + Real.exp (-Real.sqrt (c₃ * u)) ≤ 2 * (Real.exp (-(3 * L)) / (32 * (|A₀| + 1)))`. Rewrite using `[← hexpB]`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ Real.exp (-(3 * L)) / 8 * 1 := mul_le_mul_of_nonneg_left ((div_le_one ht1).2 (by linarith)) (by positivity)`.

Use `_ = Real.exp (-(3 * L)) / 8 := mul_one _`. Establish `hlog4 : Real.log 4 < 2`. Establish `e4 : Real.log 4 = 2 * Real.log 2`. Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]`. Evaluate the numerical expressions.

Use `Real.log_two_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL3' : 4 * L ≤ L ^ 3`. Use polynomial arithmetic with `[mul_nonneg hL0.le (show (0 : ℝ) ≤ L ^ 2 - 4 by nlinarith)]`. Establish `h : 3 * L + Real.log 4 ≤ 2 / 5 * u` using `by nlinarith`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show -(3 * L + Real.log 4) = -(3 * L) - Real.log 4 by ring, Real.exp_sub, Real.exp_log (by norm_num)]`.
-/
theorem final_ineq (ε c₀ c₃ A₀ C₀ L u lm ℓm ℓ : ℝ) (hε : 0 < ε) (hc₀ : 0 < c₀) (hc₃ : 0 < c₃)
    (hL1 : 2 ≤ L) (hL2 : 8 * (ε / 5 + 5 + Real.log 128) / c₀ ≤ L)
    (hL3 : 8 * (3 + Real.log (32 * (|A₀| + 1))) / c₃ ≤ L) (hL4 : Real.log (32 * (|A₀| + 1)) ≤ L)
    (hL5 : 8 * |C₀| * (Real.log 806 + ε / 5 + 1) ≤ L)
    (hu1 : (1 / 4) * L ^ 2 * ℓm ≤ u) (hu2 : (200 + 16 / c₃) * L ^ 3 ≤ u)
    (hlogu : Real.log u ≤ (ε / 5 + 2) * L)
    (hℓm : ℓm ≤ 4 * Real.exp (ε / 5 * L))
    (hlm0 : 2 ≤ lm) (hlm : lm ≤ ℓ) (hℓ : ℓ ≤ ℓm + 800 * L) :
    C₀ * lm * Real.log (lm + 2) ≤ u ∧
    16 * u * Real.exp (-(c₀ / ℓ * u)) ≤ Real.exp (-(3 * L)) / 8 ∧
    2 * |A₀| * (Real.exp (-(c₃ * u / lm)) + Real.exp (-Real.sqrt (c₃ * u))) ≤ Real.exp (-(3 * L)) / 8 ∧
    Real.exp (-(2 / 5 * u)) ≤ Real.exp (-(3 * L)) / 4 := by
  have hL0 : 0 < L := by linarith
  have hL1' : 1 ≤ L := by linarith
  have hc3L3 : 0 ≤ 16 / c₃ * L ^ 3 := by positivity
  have hu200 : 200 * L ^ 3 ≤ u := by nlinarith [hu2]
  have hu0 : 0 < u := by nlinarith [pow_pos hL0 3]
  have hkey : L ^ 2 * (ℓm + 800 * L) / 8 ≤ u := by nlinarith [hu1, hu2]
  have hℓ0 : 0 < ℓ := by linarith
  have hlm0' : 0 < lm := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have hlog_pos : 0 < Real.log (lm + 2) := Real.log_pos (by linarith)
    rcases le_or_gt C₀ 0 with hC | hC
    · have : C₀ * lm * Real.log (lm + 2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hC hlm0'.le) hlog_pos.le
      linarith
    · have hexp1 : 1 ≤ Real.exp (ε / 5 * L) := Real.one_le_exp (by positivity)
      have hlm2 : lm + 2 ≤ 806 * L * Real.exp (ε / 5 * L) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hexp1) (by linarith : (0 : ℝ) ≤ 806 * L - 4)]
      have hloglm : Real.log (lm + 2) ≤ Real.log 806 + Real.log L + ε / 5 * L := by
        calc Real.log (lm + 2) ≤ Real.log (806 * L * Real.exp (ε / 5 * L)) :=
              Real.log_le_log (by linarith) hlm2
          _ = Real.log 806 + Real.log L + ε / 5 * L := by
              rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
                Real.log_exp]
      have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
      have h806 : 0 ≤ Real.log 806 := Real.log_nonneg (by norm_num)
      have hlog2 : Real.log (lm + 2) ≤ L * (Real.log 806 + ε / 5 + 1) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hL1') h806]
      rw [abs_of_pos hC] at hL5
      have hC' : C₀ * Real.log (lm + 2) ≤ L ^ 2 / 8 := by
        calc C₀ * Real.log (lm + 2) ≤ C₀ * (L * (Real.log 806 + ε / 5 + 1)) :=
              mul_le_mul_of_nonneg_left hlog2 hC.le
          _ = L * (C₀ * (Real.log 806 + ε / 5 + 1)) := by ring
          _ ≤ L * (L / 8) := mul_le_mul_of_nonneg_left (by linarith) hL0.le
          _ = L ^ 2 / 8 := by ring
      calc C₀ * lm * Real.log (lm + 2) = lm * (C₀ * Real.log (lm + 2)) := by ring
        _ ≤ lm * (L ^ 2 / 8) := mul_le_mul_of_nonneg_left hC' hlm0'.le
        _ ≤ (ℓm + 800 * L) * (L ^ 2 / 8) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ ≤ u := by linarith [hkey]
  ·
    have hlog128 : 0 < Real.log 128 := Real.log_pos (by norm_num)
    have harg : 3 * L + Real.log 128 + Real.log u ≤ c₀ / ℓ * u := by
      have h1 : ℓ * L ^ 2 / 8 ≤ u := by
        nlinarith [hkey, mul_le_mul_of_nonneg_right (show ℓ ≤ ℓm + 800 * L by linarith) (sq_nonneg L)]
      have h2 : c₀ * L ^ 2 / 8 ≤ c₀ / ℓ * u := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hℓ0]
        nlinarith [mul_le_mul_of_nonneg_left h1 hc₀.le]
      have h3 : 3 * L + Real.log 128 + Real.log u ≤ c₀ * L ^ 2 / 8 := by
        have : ε / 5 + 5 + Real.log 128 ≤ c₀ * L / 8 := by
          rw [div_le_iff₀ hc₀] at hL2
          linarith
        nlinarith [mul_le_mul_of_nonneg_left this hL0.le, mul_nonneg (sub_nonneg.2 hL1') hlog128.le]
      linarith
    calc 16 * u * Real.exp (-(c₀ / ℓ * u)) ≤ 16 * u * Real.exp (-(3 * L + Real.log 128 + Real.log u)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by linarith)
      _ = Real.exp (-(3 * L)) / 8 := by
          rw [show -(3 * L + Real.log 128 + Real.log u) = -(3 * L) - Real.log (128 * u) by
                rw [Real.log_mul (by norm_num) hu0.ne']; ring,
            Real.exp_sub, Real.exp_log (by linarith)]
          field_simp
          ring
  ·
    obtain ⟨B, hBdef⟩ : ∃ B, B = Real.log (32 * (|A₀| + 1)) := ⟨_, rfl⟩
    rw [← hBdef] at hL3 hL4
    have hA1 : 0 < 32 * (|A₀| + 1) := by positivity
    have hB0 : 0 < B := by rw [hBdef]; exact Real.log_pos (by linarith [abs_nonneg A₀])
    have hexpB : Real.exp (-(3 * L + B)) = Real.exp (-(3 * L)) / (32 * (|A₀| + 1)) := by
      rw [show -(3 * L + B) = -(3 * L) - B by ring, Real.exp_sub, hBdef, Real.exp_log hA1]
    have hc3L : 3 + B ≤ c₃ * L / 8 := by
      rw [div_le_iff₀ hc₃] at hL3
      linarith
    have hE1 : Real.exp (-(c₃ * u / lm)) ≤ Real.exp (-(3 * L + B)) := by
      apply Real.exp_le_exp.2
      have h1 : lm * L ^ 2 / 8 ≤ u := by
        nlinarith [hkey, mul_le_mul_of_nonneg_right (show lm ≤ ℓm + 800 * L by linarith) (sq_nonneg L)]
      have h2 : c₃ * L ^ 2 / 8 ≤ c₃ * u / lm := by
        rw [le_div_iff₀ hlm0']
        nlinarith [mul_le_mul_of_nonneg_left h1 hc₃.le]
      have h3 : 3 * L + B ≤ c₃ * L ^ 2 / 8 := by
        nlinarith [mul_le_mul_of_nonneg_left hc3L hL0.le, mul_nonneg (sub_nonneg.2 hL1') hB0.le]
      linarith
    have hE2 : Real.exp (-Real.sqrt (c₃ * u)) ≤ Real.exp (-(3 * L + B)) := by
      apply Real.exp_le_exp.2
      have h0 : c₃ * ((200 + 16 / c₃) * L ^ 3) ≤ c₃ * u := mul_le_mul_of_nonneg_left hu2 hc₃.le
      have e' : c₃ * ((200 + 16 / c₃) * L ^ 3) = 200 * c₃ * L ^ 3 + 16 * L ^ 3 := by
        field_simp
      rw [e'] at h0
      have hL23 : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL1' (by norm_num)
      have h1 : (4 * L) ^ 2 ≤ c₃ * u := by nlinarith [mul_pos hc₃ (pow_pos hL0 3)]
      have h2 : 4 * L ≤ Real.sqrt (c₃ * u) := by
        have := Real.sqrt_le_sqrt h1
        rwa [Real.sqrt_sq (by linarith)] at this
      linarith
    have ht1 : 0 < |A₀| + 1 := by positivity
    have hsum : Real.exp (-(c₃ * u / lm)) + Real.exp (-Real.sqrt (c₃ * u)) ≤
        2 * (Real.exp (-(3 * L)) / (32 * (|A₀| + 1))) := by
      rw [← hexpB]
      linarith
    calc 2 * |A₀| * (Real.exp (-(c₃ * u / lm)) + Real.exp (-Real.sqrt (c₃ * u)))
        ≤ 2 * |A₀| * (2 * (Real.exp (-(3 * L)) / (32 * (|A₀| + 1)))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = Real.exp (-(3 * L)) / 8 * (|A₀| / (|A₀| + 1)) := by
          field_simp
          ring
      _ ≤ Real.exp (-(3 * L)) / 8 * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one ht1).2 (by linarith)) (by positivity)
      _ = Real.exp (-(3 * L)) / 8 := mul_one _
  ·
    have hlog4 : Real.log 4 < 2 := by
      have e4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      have := Real.log_two_lt_d9
      linarith
    have hL3' : 4 * L ≤ L ^ 3 := by
      nlinarith [mul_nonneg hL0.le (show (0 : ℝ) ≤ L ^ 2 - 4 by nlinarith)]
    have h : 3 * L + Real.log 4 ≤ 2 / 5 * u := by nlinarith
    calc Real.exp (-(2 / 5 * u)) ≤ Real.exp (-(3 * L + Real.log 4)) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp (-(3 * L)) / 4 := by
          rw [show -(3 * L + Real.log 4) = -(3 * L) - Real.log 4 by ring, Real.exp_sub,
            Real.exp_log (by norm_num)]

/- English proof (translation)
Establish `h` using `(isLittleO_log_rpow_rpow_atTop 3 ha).bound (by positivity : (0 : ℝ) < 1 / K)`. Take `⟨x₂, hx₂⟩` from `Filter.eventually_atTop.1 (h.and (Filter.eventually_gt_atTop 0))`. Use `⟨x₂, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hx₂ x hx`. Rewrite `h1` using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos h2 a)]`.

Establish `h3 : Real.log x ^ 3 = Real.log x ^ (3 : ℝ)`. Rewrite using `[← Real.rpow_natCast]`. Evaluate the numerical expressions. Rewrite using `[h3]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eventually_log_cube (K a : ℝ) (hK : 0 < K) (ha : 0 < a) :
    ∃ x₂ : ℝ, ∀ x : ℝ, x₂ ≤ x → K * Real.log x ^ 3 ≤ x ^ a := by
  have h := (isLittleO_log_rpow_rpow_atTop 3 ha).bound (by positivity : (0 : ℝ) < 1 / K)
  obtain ⟨x₂, hx₂⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_gt_atTop 0))
  refine ⟨x₂, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx₂ x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos h2 a)] at h1
  have h3 : Real.log x ^ 3 = Real.log x ^ (3 : ℝ) := by
    rw [← Real.rpow_natCast]
    norm_num
  rw [h3]
  calc K * Real.log x ^ (3 : ℝ) ≤ K * |Real.log x ^ (3 : ℝ)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hK.le
    _ ≤ K * (1 / K * x ^ a) := mul_le_mul_of_nonneg_left h1 hK.le
    _ = x ^ a := by field_simp

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
