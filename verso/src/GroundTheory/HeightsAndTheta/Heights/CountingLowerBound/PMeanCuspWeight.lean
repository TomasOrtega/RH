import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real MeasureTheory Filter Topology

noncomputable section

/- English proof (translation)
The claim follows from `max_le (add_nonneg (le_max_left 0 a) hb) (by linarith [le_max_right 0 a])`.
-/
theorem max_zero_add_le_of_nonneg {a b : ℝ} (hb : 0 ≤ b) : max 0 (a + b) ≤ max 0 a + b :=
  max_le (add_nonneg (le_max_left 0 a) hb) (by linarith [le_max_right 0 a])

/- English proof (translation)
Introduce `X _ μ U lam f j' vr rd h`. Use `h.isProbability` as an intermediate fact. Establish `hf : (1 : ℝ) ≤ f` using `by exact_mod_cast h.one_le_f`. Establish `hj : (1 : ℝ) ≤ j'` using `by exact_mod_cast h.one_le_j'`. Establish `hfj : 0 ≤ (f : ℝ) * j'` using `by positivity`.

Establish `hvr0 : 0 < vr` using `lt_of_lt_of_le one_pos h.one_le_vr`. Establish `hlogvr : 0 ≤ log vr` using `Real.log_nonneg h.one_le_vr`. Establish `hr0 : 0 < vr ^ (-(1 / 2 : ℝ))` using `Real.rpow_pos_of_pos hvr0 _`. Establish `hlogr : log (vr ^ (-(1 / 2 : ℝ))) = -(1 / 2) * log vr` using `Real.log_rpow hvr0 _`. Establish `key : ∀ z, max 0 (log (1 / lam z)) ≤ max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr`.

Introduce `z`. Establish `hl` using `h.lam_pos z`. Establish `e : log (1 / lam z) = log (vr ^ (-(1 / 2 : ℝ)) / lam z) + 1 / 2 * log vr`. Rewrite using `[Real.log_div one_ne_zero hl.ne', Real.log_div hr0.ne' hl.ne', hlogr, Real.log_one]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `max_zero_add_le_of_nonneg (by positivity)`. Use `set L : ℝ := log (2 * f * j' * rd) with hL`. Use `set g : X → ℝ := fun z => (f : ℝ) * j' * (2 * (max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr) + L) with hg`. Establish `hUg : ∀ z, U z ≤ g z`.

Introduce `z`. Use `(h.U_le z).trans (mul_le_mul_of_nonneg_left ?_ hfj)` and prove the remaining obligations. Combine the linear relations using `[key z]`. Establish `hint_h` using `h.logPlus_integrable`. Establish `hint : Integrable g μ` using `(((hint_h.add (integrable_const (1 / 2 * log vr))).const_mul 2).add (integrable_const L)).const_mul _`.

Establish `hmono : ∫ z, U z ∂μ ≤ ∫ z, g z ∂μ` using `integral_mono_of_nonneg (ae_of_all _ h.U_nonneg) hint (ae_of_all _ hUg)`. Establish `hval : ∫ z, g z ∂μ = (f : ℝ) * j' * (2 * ((∫ z, max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) ∂μ) + 1 / 2 * log vr) + L)`. Establish `h1 : Integrable (fun z => max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr) μ` using `hint_h.add (integrable_const _)`. Establish `h2 : Integrable (fun z => 2 * (max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr)) μ` using `h1.const_mul 2`. Rewrite using `[hg, integral_const_mul, integral_add h2 (integrable_const L), integral_const_mul, integral_add hint_h (integrable_const _), integral_const, integral_const, probReal_univ, one_smul, one_smul]`.

Rewrite `hmono` using `[hval]`. Use `hmono.trans (mul_le_mul_of_nonneg_left ?_ hfj)` and prove the remaining obligations. Combine the linear relations using `[h.logPlus_mean]`.
-/
theorem MeanCuspWeight.proof : MeanCuspWeight.Statement := by
  intro X _ μ U lam f j' vr rd h
  have := h.isProbability
  have hf : (1 : ℝ) ≤ f := by exact_mod_cast h.one_le_f
  have hj : (1 : ℝ) ≤ j' := by exact_mod_cast h.one_le_j'
  have hfj : 0 ≤ (f : ℝ) * j' := by positivity
  have hvr0 : 0 < vr := lt_of_lt_of_le one_pos h.one_le_vr
  have hlogvr : 0 ≤ log vr := Real.log_nonneg h.one_le_vr
  have hr0 : 0 < vr ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hvr0 _
  have hlogr : log (vr ^ (-(1 / 2 : ℝ))) = -(1 / 2) * log vr := Real.log_rpow hvr0 _

  have key : ∀ z, max 0 (log (1 / lam z)) ≤
      max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr := by
    intro z
    have hl := h.lam_pos z
    have e : log (1 / lam z) = log (vr ^ (-(1 / 2 : ℝ)) / lam z) + 1 / 2 * log vr := by
      rw [Real.log_div one_ne_zero hl.ne', Real.log_div hr0.ne' hl.ne', hlogr, Real.log_one]
      ring
    rw [e]
    exact max_zero_add_le_of_nonneg (by positivity)
  set L : ℝ := log (2 * f * j' * rd) with hL
  set g : X → ℝ := fun z =>
    (f : ℝ) * j' * (2 * (max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr) + L) with hg
  have hUg : ∀ z, U z ≤ g z := by
    intro z
    refine (h.U_le z).trans (mul_le_mul_of_nonneg_left ?_ hfj)
    linarith [key z]
  have hint_h := h.logPlus_integrable
  have hint : Integrable g μ :=
    (((hint_h.add (integrable_const (1 / 2 * log vr))).const_mul 2).add
      (integrable_const L)).const_mul _
  have hmono : ∫ z, U z ∂μ ≤ ∫ z, g z ∂μ :=
    integral_mono_of_nonneg (ae_of_all _ h.U_nonneg) hint (ae_of_all _ hUg)
  have hval : ∫ z, g z ∂μ = (f : ℝ) * j' *
      (2 * ((∫ z, max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) ∂μ) + 1 / 2 * log vr) + L) := by
    have h1 : Integrable (fun z => max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr) μ :=
      hint_h.add (integrable_const _)
    have h2 : Integrable
        (fun z => 2 * (max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr)) μ :=
      h1.const_mul 2
    rw [hg, integral_const_mul, integral_add h2 (integrable_const L), integral_const_mul,
      integral_add hint_h (integrable_const _), integral_const, integral_const, probReal_univ,
      one_smul, one_smul]
  rw [hval] at hmono
  refine hmono.trans (mul_le_mul_of_nonneg_left ?_ hfj)
  linarith [h.logPlus_mean]

end

end GroundTheory.Heights₂.Heights.LowerBound
