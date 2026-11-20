import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableDet

noncomputable section

open MeasureTheory Matrix Complex Ad3 Ad3.LR Ad3.K.GL2LocalData Ad3.K.GL2LocalData.WR GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst.BndFin

namespace GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst.BndFin.DInt

def gam (s t : ℝ) : ℝ :=
  if 0 < t then t ^ s * Real.exp (-(2 * Real.pi) * t) else 0

/- English proof (translation)
Unfold `gam`. Use `split_ifs with h`. Use `h.le` as an intermediate fact. Check the signs of the components of the expression. Conclude with `le_rfl`.
-/
theorem gam_nonneg (s t : ℝ) : 0 ≤ gam s t := by
  unfold gam; split_ifs with h
  · have := h.le; positivity
  · exact le_rfl

/- English proof (translation)
Unfold `gam`. Conclude with `Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const`.
-/
theorem measurable_gam (s : ℝ) : Measurable (gam s) := by
  unfold gam
  exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const

/- English proof (translation)
Unfold `dK`. Conclude with `Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const`.
-/
theorem measurable_dK (β K N : ℝ) : Measurable (dK β K N) := by
  unfold dK
  exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const

/- English proof (translation)
Establish `hb : (0 : ℝ) < 2 * Real.pi` using `by positivity`. Establish `h` using `integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s) (b := 2 * Real.pi) hs zero_lt_one hb`. Simplify using `only [Real.rpow_one] at h`. Establish `hi : Integrable (gam s)`. Establish `: gam s = (Set.Ioi (0 : ℝ)).indicator (fun t => t ^ s * Real.exp (-(2 * Real.pi) * t))`.

Use function extensionality and compare the values at `t`. Simplify using `only [gam, Set.indicator, Set.mem_Ioi]`. Rewrite using `[this]`. Conclude with `(integrable_indicator_iff measurableSet_Ioi).2 h`. Conclude with `hi.lintegral_lt_top.ne`.
-/
theorem lintegral_gam_ne_top {s : ℝ} (hs : -1 < s) :
    ∫⁻ t, ENNReal.ofReal (gam s t) ≠ ⊤ := by
  have hb : (0 : ℝ) < 2 * Real.pi := by positivity
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s) (b := 2 * Real.pi) hs zero_lt_one hb
  simp only [Real.rpow_one] at h
  have hi : Integrable (gam s) := by
    have : gam s = (Set.Ioi (0 : ℝ)).indicator
        (fun t => t ^ s * Real.exp (-(2 * Real.pi) * t)) := by
      funext t
      simp only [gam, Set.indicator, Set.mem_Ioi]
    rw [this]
    exact (integrable_indicator_iff measurableSet_Ioi).2 h
  exact hi.lintegral_lt_top.ne

/- English proof (translation)
Establish `hm : Measurable fun d : ℝ => N⁻¹ * d` using `by fun_prop`. Establish `h` using `Real.map_volume_mul_left (a := N⁻¹) (inv_ne_zero hN.ne')`. Rewrite using `[← lintegral_map hf hm, h, lintegral_smul_measure, inv_inv, abs_of_pos hN]`. Both sides reduce to the same expression.
-/
theorem lintegral_scale {f : ℝ → ENNReal} (hf : Measurable f) {N : ℝ} (hN : 0 < N) :
    ∫⁻ d, f (N⁻¹ * d) = ENNReal.ofReal N * ∫⁻ t, f t := by
  have hm : Measurable fun d : ℝ => N⁻¹ * d := by fun_prop
  have h := Real.map_volume_mul_left (a := N⁻¹) (inv_ne_zero hN.ne')
  rw [← lintegral_map hf hm, h, lintegral_smul_measure, inv_inv, abs_of_pos hN]
  rfl

/- English proof (translation)
Rewrite using `[Real.mul_rpow hN.le ht.le, Real.rpow_sub hN, Real.rpow_sub ht, Real.rpow_add ht]`. Simplify using `only [Real.rpow_two]`. Establish `h1` using `hN.ne'`. Establish `h2` using `ht.ne'`. Clear the denominators using the available nonvanishing facts.
-/
theorem real_key {β K N t : ℝ} (hN : 0 < N) (ht : 0 < t) (E : ℝ) :
    ((N * t) ^ 2)⁻¹ * ((N * t) ^ β * t ^ K * E) = N ^ (β - 2) * (t ^ (β + K - 2) * E) := by
  rw [Real.mul_rpow hN.le ht.le, Real.rpow_sub hN, Real.rpow_sub ht, Real.rpow_add ht]
  simp only [Real.rpow_two]
  have h1 := hN.ne'
  have h2 := ht.ne'
  field_simp

/- English proof (translation)
Distinguish the cases in `hd : 0 < d`. Establish `ht : 0 < N⁻¹ * d` using `by positivity`. Establish `hd' : d = N * (N⁻¹ * d)` using `by field_simp`. Establish `hdN : d / N = N⁻¹ * d` using `by field_simp`. Rewrite using `[← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]`.

Use `congr 1`. Simplify using `only [dK, gam, if_pos hd, if_pos ht, hdN]`. Establish `h` using `real_key (β := β) (K := K) hN ht (Real.exp (-2 * Real.pi * (N⁻¹ * d)))`. Rewrite `h` using `[← hd']`. Rewrite using `[h]`.

Simplify using `only [neg_mul]`. Establish `ht : ¬ 0 < N⁻¹ * d`. Conclude with `not_lt.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 hd))`. Simplify using `[dK, gam, if_neg hd, if_neg ht]`.
-/
theorem pointwise (β K : ℝ) {N : ℝ} (hN : 0 < N) (d : ℝ) :
    ENNReal.ofReal (d ^ 2)⁻¹ * ENNReal.ofReal (dK β K N d) =
      ENNReal.ofReal (N ^ (β - 2)) * ENNReal.ofReal (gam (β + K - 2) (N⁻¹ * d)) := by
  by_cases hd : 0 < d
  · have ht : 0 < N⁻¹ * d := by positivity
    have hd' : d = N * (N⁻¹ * d) := by field_simp
    have hdN : d / N = N⁻¹ * d := by field_simp
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [dK, gam, if_pos hd, if_pos ht, hdN]
    have h := real_key (β := β) (K := K) hN ht (Real.exp (-2 * Real.pi * (N⁻¹ * d)))
    rw [← hd'] at h
    rw [h]
    simp only [neg_mul]
  · have ht : ¬ 0 < N⁻¹ * d := by
      exact not_lt.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 hd))
    simp [dK, gam, if_neg hd, if_neg ht]

/- English proof (translation)
Introduce `β K hβ hK`. Use `⟨∫⁻ t, ENNReal.ofReal (gam (β + K - 2) t), lintegral_gam_ne_top (by linarith), ?_⟩` and prove the remaining obligations. Introduce `N hN`. Establish `hdens : Measurable fun d : ℝ => ENNReal.ofReal (d ^ 2)⁻¹` using `by fun_prop`. Establish `hg : Measurable fun t : ℝ => ENNReal.ofReal (gam (β + K - 2) t)` using `(measurable_gam _).ennreal_ofReal`.

Rewrite using `[lintegral_withDensity_eq_lintegral_mul _ hdens (measurable_dK β K N).ennreal_ofReal]`. Simplify using `only [Pi.mul_apply, pointwise β K hN]`. Establish `hc : Measurable fun d : ℝ => ENNReal.ofReal (gam (β + K - 2) (N⁻¹ * d))` using `((measurable_gam _).comp (by fun_prop : Measurable fun d : ℝ => N⁻¹ * d)).ennreal_ofReal`. Establish `hs : ∫⁻ d, ENNReal.ofReal (gam (β + K - 2) (N⁻¹ * d)) = ENNReal.ofReal N * ∫⁻ t, ENNReal.ofReal (gam (β + K - 2) t)` using `lintegral_scale hg hN`. Rewrite using `[lintegral_const_mul _ hc, hs]`.

Establish `hpow : N ^ (β - 1) = N ^ (β - 2) * N`. Rewrite using `[show β - 1 = (β - 2) + 1 by ring, Real.rpow_add hN, Real.rpow_one]`. Rewrite using `[hpow, ENNReal.ofReal_mul (by positivity)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ β K : ℝ, 0 < β → 2 ≤ K → ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ N : ℝ, 0 < N →
    ∫⁻ d, ENNReal.ofReal (dK β K N d) ∂(volume.withDensity fun d : ℝ => ENNReal.ofReal (d ^ 2)⁻¹) =
      C * ENNReal.ofReal (N ^ (β - 1)) := by
  intro β K hβ hK
  refine ⟨∫⁻ t, ENNReal.ofReal (gam (β + K - 2) t), lintegral_gam_ne_top (by linarith), ?_⟩
  intro N hN
  have hdens : Measurable fun d : ℝ => ENNReal.ofReal (d ^ 2)⁻¹ := by fun_prop
  have hg : Measurable fun t : ℝ => ENNReal.ofReal (gam (β + K - 2) t) :=
    (measurable_gam _).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hdens (measurable_dK β K N).ennreal_ofReal]
  simp only [Pi.mul_apply, pointwise β K hN]
  have hc : Measurable fun d : ℝ => ENNReal.ofReal (gam (β + K - 2) (N⁻¹ * d)) :=
    ((measurable_gam _).comp (by fun_prop : Measurable fun d : ℝ => N⁻¹ * d)).ennreal_ofReal
  have hs : ∫⁻ d, ENNReal.ofReal (gam (β + K - 2) (N⁻¹ * d)) =
      ENNReal.ofReal N * ∫⁻ t, ENNReal.ofReal (gam (β + K - 2) t) := lintegral_scale hg hN
  rw [lintegral_const_mul _ hc, hs]
  have hpow : N ^ (β - 1) = N ^ (β - 2) * N := by
    rw [show β - 1 = (β - 2) + 1 by ring, Real.rpow_add hN, Real.rpow_one]
  rw [hpow, ENNReal.ofReal_mul (by positivity)]
  ring

end GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst.BndFin.DInt

end
