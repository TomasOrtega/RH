import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open MeasureTheory Metric Set
open ReciprocityTheory.AnForm.A

noncomputable section

/- English proof (translation)
Rewrite using `[Measure.real, volume_pi_closedBall x hr]`. Simplify using `only [Complex.volume_closedBall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr]`. Simplify using `[mul_comm]`.
-/
theorem volume_real_closedBall_polydisc {D : ℕ} (x : Fin D → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (closedBall x r) = (Real.pi * r ^ 2) ^ D := by
  rw [Measure.real, volume_pi_closedBall x hr]
  simp only [Complex.volume_closedBall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr]
  simp [mul_comm]

/- English proof (translation)
Introduce `D ρ b U u z t hU hu ht hzU hb`. Use `set M2 := polyMax u z (2 * t)`. Use `set M4 := polyMax u z (t / 4)`. Take `⟨-, -, hatt, -⟩` from `h1 D U u z (2 * t) hU hu (by positivity) hzU`. Take `⟨x, hx, hux⟩` from `hatt (t / 4) (by positivity) (by linarith)`.

Rewrite `hx` using `[mem_closedBall]`. Use `set B := closedBall x (3 / 2 * t) with hBdef`. Establish `hBz : B ⊆ closedBall z (2 * t)` using `closedBall_subset_closedBall' (by linarith)`. Establish `hzB : closedBall z t ⊆ B` using `closedBall_subset_closedBall' (by rw [dist_comm]; linarith)`. Take `⟨hint, hmean⟩` from `h0 D U u x (3 / 2 * t) hU hu (by positivity) (hBz.trans hzU)`.

Rewrite `hint`, `hmean` using `[← hBdef]`. Establish `hle2 : ∀ p ∈ B, u p ≤ M2` using `fun p hp => le_polyMax hu.1 hzU (hBz hp)`. Establish `hb0 : 0 ≤ b` using `(ρ.nonneg 0).trans (hb 0)`. Establish `hV : volume.real B = (Real.pi * (3 / 2 * t) ^ 2) ^ D` using `volume_real_closedBall_polydisc x (by positivity)`. Establish `hVpos : 0 < volume.real B` using `by rw [hV]; positivity`.

Establish `hcint : IntegrableOn (fun _ => M2) B` using `integrableOn_const measure_closedBall_lt_top.ne`. Establish `hIB : ∫ p in B, (M2 - u p) ≤ volume.real B * (M2 - M4)`. Rewrite using `[integral_sub hcint hint, setIntegral_const, smul_eq_mul]`. Rewrite `hmean` using `[setAverage_eq, smul_eq_mul]`. Establish `h` using `mul_le_mul_of_nonneg_left hmean hVpos.le`.

Rewrite `h` using `[← mul_assoc, mul_inv_cancel₀ hVpos.ne', one_mul]`. Rewrite using `[show M4 = u x from hux.symm]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set g : (Fin D → ℂ) → ℝ := B.indicator (fun p => M2 - u p) with hgdef`. Establish `hg0 : ∀ q, 0 ≤ g q`.

Introduce `q`. Distinguish the cases in `hq : q ∈ B`. Rewrite using `[hgdef, indicator_of_mem hq]`. Conclude with `sub_nonneg.2 (hle2 q hq)`. Rewrite using `[hgdef, indicator_of_notMem hq]`.

Establish `hgint : Integrable g` using `(integrable_indicator_iff measurableSet_closedBall).2 (hcint.sub hint)`. Establish `hBind : Integrable (B.indicator u)` using `(integrable_indicator_iff measurableSet_closedBall).2 hint`. Use `set c : ℝ := (t ^ (2 * D))⁻¹ * b with hcdef`. Establish `hc0 : 0 ≤ c` using `by positivity`. Establish `hsc : ∀ y, ρ.scaled t y ≤ c` using `fun y => mul_le_mul_of_nonneg_left (hb _) (by positivity)`.

Establish `key : ∫ y, (ρ.scaled t y * M2 - ρ.scaled t y * B.indicator u (z - y)) ≤ ∫ y, c * g (z - y)`. Use `integral_mono (((integrable_scaled ρ ht).mul_const M2).sub (integrable_kC ρ ht hBind z)) ((hgint.comp_sub_left z).const_mul c) fun y => ?_` and prove the remaining obligations. Distinguish the cases in `hy : ρ.scaled t y = 0`. Simplify using `only [hy, zero_mul, sub_zero]`. Conclude with `mul_nonneg hc0 (hg0 _)`.

Establish `hm : z - y ∈ B` using `hzB (mem_ball_sub ρ ht hy z)`. Simplify using `only [hgdef, indicator_of_mem hm]`. Rewrite using `[← mul_sub]`. Conclude with `mul_le_mul_of_nonneg_right (hsc y) (sub_nonneg.2 (hle2 _ hm))`. Establish `hLHS : ∫ y, (ρ.scaled t y * M2 - ρ.scaled t y * B.indicator u (z - y)) = M2 - molli ρ t u z`.

Rewrite using `[integral_sub ((integrable_scaled ρ ht).mul_const M2) (integrable_kC ρ ht hBind z), integral_mul_const, integral_scaled ρ ht, one_mul, molli_eq_C ρ ht hzB (φ := u)]`. Establish `hRHS : ∫ y, c * g (z - y) = c * ∫ p in B, (M2 - u p)`. Rewrite using `[integral_const_mul]`. Use `congr 1`. Use `(Measure.measurePreserving_sub_left volume z).integral_comp (Homeomorph.subLeft z).measurableEmbedding g` as an intermediate fact.

Rewrite using `[this, hgdef, integral_indicator measurableSet_closedBall]`. Establish `hcV : c * volume.real B = Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b`. Rewrite using `[hV, hcdef]`. Establish `ht' : t ^ (2 * D) ≠ 0` using `by positivity`. Rewrite using `[mul_pow, ← pow_mul, mul_pow, pow_mul (3 / 2 : ℝ) 2 D]`.

Clear the denominators using the available nonvanishing facts. Establish `hfin` using `mul_le_mul_of_nonneg_left hIB hc0`. Establish `e : c * (volume.real B * (M2 - M4)) = Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b * (M2 - M4)`. Rewrite using `[← hcV]`. Expand and normalize the polynomial expressions, which then agree.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem MollifiedLowerBound.proof (h0 : SubMeanPolydiscStatement)
    (h1 : PolyMaxLogConvexStatement) : MollifiedLowerBound.Statement := by
  intro D ρ b U u z t hU hu ht hzU hb
  set M2 := polyMax u z (2 * t)
  set M4 := polyMax u z (t / 4)
  obtain ⟨-, -, hatt, -⟩ := h1 D U u z (2 * t) hU hu (by positivity) hzU
  obtain ⟨x, hx, hux⟩ := hatt (t / 4) (by positivity) (by linarith)
  rw [mem_closedBall] at hx
  set B := closedBall x (3 / 2 * t) with hBdef
  have hBz : B ⊆ closedBall z (2 * t) :=
    closedBall_subset_closedBall' (by linarith)
  have hzB : closedBall z t ⊆ B :=
    closedBall_subset_closedBall' (by rw [dist_comm]; linarith)
  obtain ⟨hint, hmean⟩ := h0 D U u x (3 / 2 * t) hU hu (by positivity) (hBz.trans hzU)
  rw [← hBdef] at hint hmean
  have hle2 : ∀ p ∈ B, u p ≤ M2 := fun p hp => le_polyMax hu.1 hzU (hBz hp)
  have hb0 : 0 ≤ b := (ρ.nonneg 0).trans (hb 0)
  have hV : volume.real B = (Real.pi * (3 / 2 * t) ^ 2) ^ D :=
    volume_real_closedBall_polydisc x (by positivity)
  have hVpos : 0 < volume.real B := by rw [hV]; positivity
  have hcint : IntegrableOn (fun _ => M2) B := integrableOn_const measure_closedBall_lt_top.ne

  have hIB : ∫ p in B, (M2 - u p) ≤ volume.real B * (M2 - M4) := by
    rw [integral_sub hcint hint, setIntegral_const, smul_eq_mul]
    rw [setAverage_eq, smul_eq_mul] at hmean
    have h := mul_le_mul_of_nonneg_left hmean hVpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hVpos.ne', one_mul] at h
    rw [show M4 = u x from hux.symm]
    linarith

  set g : (Fin D → ℂ) → ℝ := B.indicator (fun p => M2 - u p) with hgdef
  have hg0 : ∀ q, 0 ≤ g q := by
    intro q
    by_cases hq : q ∈ B
    · rw [hgdef, indicator_of_mem hq]; exact sub_nonneg.2 (hle2 q hq)
    · rw [hgdef, indicator_of_notMem hq]
  have hgint : Integrable g :=
    (integrable_indicator_iff measurableSet_closedBall).2 (hcint.sub hint)
  have hBind : Integrable (B.indicator u) :=
    (integrable_indicator_iff measurableSet_closedBall).2 hint
  set c : ℝ := (t ^ (2 * D))⁻¹ * b with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hsc : ∀ y, ρ.scaled t y ≤ c := fun y =>
    mul_le_mul_of_nonneg_left (hb _) (by positivity)
  have key : ∫ y, (ρ.scaled t y * M2 - ρ.scaled t y * B.indicator u (z - y)) ≤
      ∫ y, c * g (z - y) := by
    refine integral_mono (((integrable_scaled ρ ht).mul_const M2).sub
      (integrable_kC ρ ht hBind z)) ((hgint.comp_sub_left z).const_mul c) fun y => ?_
    by_cases hy : ρ.scaled t y = 0
    · simp only [hy, zero_mul, sub_zero]
      exact mul_nonneg hc0 (hg0 _)
    · have hm : z - y ∈ B := hzB (mem_ball_sub ρ ht hy z)
      simp only [hgdef, indicator_of_mem hm]
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_right (hsc y) (sub_nonneg.2 (hle2 _ hm))
  have hLHS : ∫ y, (ρ.scaled t y * M2 - ρ.scaled t y * B.indicator u (z - y)) =
      M2 - molli ρ t u z := by
    rw [integral_sub ((integrable_scaled ρ ht).mul_const M2) (integrable_kC ρ ht hBind z),
      integral_mul_const, integral_scaled ρ ht, one_mul, molli_eq_C ρ ht hzB (φ := u)]
  have hRHS : ∫ y, c * g (z - y) = c * ∫ p in B, (M2 - u p) := by
    rw [integral_const_mul]
    congr 1
    have := (Measure.measurePreserving_sub_left volume z).integral_comp
      (Homeomorph.subLeft z).measurableEmbedding g
    rw [this, hgdef, integral_indicator measurableSet_closedBall]
  have hcV : c * volume.real B = Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b := by
    rw [hV, hcdef]
    have ht' : t ^ (2 * D) ≠ 0 := by positivity
    rw [mul_pow, ← pow_mul, mul_pow, pow_mul (3 / 2 : ℝ) 2 D]
    field_simp
  have hfin := mul_le_mul_of_nonneg_left hIB hc0
  have e : c * (volume.real B * (M2 - M4)) =
      Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b * (M2 - M4) := by
    rw [← hcV]; ring
  linarith

/- English proof (translation)
The claim follows from `MollifiedLowerBound.proof subMeanPolydisc_thm polyMaxLogConvex_thm`.
-/
theorem MollifiedLowerBound.closed : MollifiedLowerBound.Statement :=
  MollifiedLowerBound.proof subMeanPolydisc_thm polyMaxLogConvex_thm

end

end GroundTheory.Heights₂.Heights.Regular
