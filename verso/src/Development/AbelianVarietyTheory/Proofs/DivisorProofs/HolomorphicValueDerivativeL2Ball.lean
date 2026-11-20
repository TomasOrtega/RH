import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFderivLeOfBoundedGen
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

noncomputable section

/- English proof (translation)
Establish `hu' : DifferentiableOn ℂ (fun y => u (x + y)) (ball 0 s)`. Introduce `y hy`. Establish `hxy : x + y ∈ ball x s` using `by simpa [mem_ball, dist_eq_norm] using hy`. Conclude with `((hu.differentiableAt (isOpen_ball.mem_nhds hxy)).comp y ((differentiable_const x).add differentiable_id y)).differentiableWithinAt`. Establish `hρm : Measurable fun t : ℝ => (Set.Iio s).indicator (fun _ => (1 : ℝ≥0∞)) t` using `measurable_const.indicator measurableSet_Iio`.

Establish `h` using `ReciprocityTheory.L2DbarEstimates.mv n s _ _ hu' hρm (fun t ht => Set.indicator_of_notMem (by simpa using ht) _)`. Establish `e1 : ∀ y : V n, (Set.Iio s).indicator (fun _ => (1 : ℝ≥0∞)) ‖y‖ = (ball (0 : V n) s).indicator 1 y`. Introduce `y`. Distinguish the cases in `hy : ‖y‖ < s`. Rewrite using `[Set.indicator_of_mem (by simpa using hy), Set.indicator_of_mem (by simpa using hy)]; rfl`.

Rewrite using `[Set.indicator_of_notMem (by simpa using hy), Set.indicator_of_notMem (by simpa using hy)]`. Simplify using `only [add_zero, e1] at h`. Rewrite `h` using `[lintegral_indicator_one measurableSet_ball]`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[← lintegral_indicator measurableSet_ball, ← lintegral_add_left_eq_self (fun v => (ball x s).indicator (fun v => ENNReal.ofReal (‖u v‖ ^ 2)) v) x]`.

Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Distinguish the cases in `hy : y ∈ ball (0 : V n) s`. Establish `hxy : x + y ∈ ball x s` using `by simpa [mem_ball, dist_eq_norm] using hy`. Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem hxy]`. Simplify using the standard rewrite rules.

Establish `hxy : x + y ∉ ball x s` using `by simpa [mem_ball, dist_eq_norm] using hy`. Rewrite using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hxy]`. Simplify using the standard rewrite rules.
-/
theorem l2ball_sq_mul_vol_le {n : ℕ} {x : V n} {s : ℝ} (u : V n → ℂ)
    (hu : DifferentiableOn ℂ u (ball x s)) :
    ENNReal.ofReal (‖u x‖ ^ 2) * volume (ball (0 : V n) s) ≤
      ∫⁻ v in ball x s, ENNReal.ofReal (‖u v‖ ^ 2) := by
  have hu' : DifferentiableOn ℂ (fun y => u (x + y)) (ball 0 s) := by
    intro y hy
    have hxy : x + y ∈ ball x s := by simpa [mem_ball, dist_eq_norm] using hy
    exact ((hu.differentiableAt (isOpen_ball.mem_nhds hxy)).comp y
      ((differentiable_const x).add differentiable_id y)).differentiableWithinAt
  have hρm : Measurable fun t : ℝ => (Set.Iio s).indicator (fun _ => (1 : ℝ≥0∞)) t :=
    measurable_const.indicator measurableSet_Iio
  have h := ReciprocityTheory.L2DbarEstimates.mv n s _ _ hu' hρm
    (fun t ht => Set.indicator_of_notMem (by simpa using ht) _)
  have e1 : ∀ y : V n, (Set.Iio s).indicator (fun _ => (1 : ℝ≥0∞)) ‖y‖ =
      (ball (0 : V n) s).indicator 1 y := by
    intro y
    by_cases hy : ‖y‖ < s
    · rw [Set.indicator_of_mem (by simpa using hy), Set.indicator_of_mem (by simpa using hy)]; rfl
    · rw [Set.indicator_of_notMem (by simpa using hy), Set.indicator_of_notMem (by simpa using hy)]
  simp only [add_zero, e1] at h
  rw [lintegral_indicator_one measurableSet_ball] at h
  refine h.trans (le_of_eq ?_)
  rw [← lintegral_indicator measurableSet_ball,
    ← lintegral_add_left_eq_self (fun v => (ball x s).indicator (fun v => ENNReal.ofReal (‖u v‖ ^ 2)) v) x]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ ball (0 : V n) s
  · have hxy : x + y ∈ ball x s := by simpa [mem_ball, dist_eq_norm] using hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hxy]; simp
  · have hxy : x + y ∉ ball x s := by simpa [mem_ball, dist_eq_norm] using hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hxy]; simp

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded`. Consider the case `exact _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded`. Consider the case `(apply _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded ..)`.
-/
theorem norm_fderiv_le_of_ball {n : ℕ} {p : V n} {ρ R M : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (u : V n → ℂ) (hu : DifferentiableOn ℂ u (ball p R)) (hM : ∀ x ∈ ball p R, ‖u x‖ ≤ M) :
    ‖fderiv ℂ u p‖ ≤ M / ρ := by
  first
  | exact @_root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded
  | exact _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded
  | (apply _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> assumption)
  | (intros; apply _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded ..)

/- English proof (translation)
Introduce `n r hr`. Use `set β : ℝ := (volume (ball (0 : V n) (r / 2))).toReal with hβdef`. Establish `hβ : 0 < β` using `ENNReal.toReal_pos (measure_ball_pos volume _ (by linarith)).ne' measure_ball_lt_top.ne`. Establish `hV : volume (ball (0 : V n) (r / 2)) = ENNReal.ofReal β` using `(ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm`. Use `⟨(1 + 16 / r ^ 2) / β, by positivity, fun p u hu => ?_⟩` and prove the remaining obligations.

Use `set I := ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) with hIdef`. Distinguish the cases in `hI : I = ⊤`. Rewrite using `[hI, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']; exact le_top`. Use `set J := I.toReal with hJ`. Establish `hI' : I = ENNReal.ofReal J` using `(ENNReal.ofReal_toReal hI).symm`.

Establish `hx : ∀ x ∈ ball p (r / 2), ‖u x‖ ^ 2 ≤ J / β`. Introduce `x hx`. Establish `hsub : ball x (r / 2) ⊆ ball p r`. Apply `ball_subset_ball'` to reduce the goal to its premises. Rewrite `hx` using `[mem_ball]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2` using `(l2ball_sq_mul_vol_le u (hu.mono hsub)).trans (lintegral_mono_set hsub)`. Rewrite `h2` using `[hV, ← ENNReal.ofReal_mul (sq_nonneg _), ← hIdef, hI']`. Rewrite using `[le_div_iff₀ hβ]`. Conclude with `(ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 h2`.

Use `set M := Real.sqrt (J / β) with hMdef`. Establish `hJβ : 0 ≤ J / β` using `div_nonneg ENNReal.toReal_nonneg hβ.le`. Establish `hMx : ∀ x ∈ ball p (r / 2), ‖u x‖ ≤ M`. Introduce `x hx'`. Use `Real.sqrt_le_sqrt (hx x hx')` as an intermediate fact.

Rewrite `this` using `[Real.sqrt_sq (norm_nonneg _)]`. Then use the resulting hypothesis. Establish `hD` using `norm_fderiv_le_of_ball (ρ := r / 4) (by positivity) (by linarith) u (hu.mono (ball_subset_ball (by linarith))) hMx`. Establish `hD2 : ‖fderiv ℂ u p‖ ^ 2 ≤ 16 / r ^ 2 * (J / β)`. Use `pow_le_pow_left₀ (norm_nonneg _) hD 2` as an intermediate fact. Use `this.trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[div_pow, Real.sq_sqrt hJβ]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hp` using `hx p (mem_ball_self (by linarith))`. Rewrite using `[hI', ← ENNReal.ofReal_mul (by positivity)]`.

Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem l2_value_deriv_ball :
    ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : V n) (u : V n → ℂ),
      DifferentiableOn ℂ u (ball p r) →
        ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2) ≤
          ENNReal.ofReal C * ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) := by
  intro n r hr
  set β : ℝ := (volume (ball (0 : V n) (r / 2))).toReal with hβdef
  have hβ : 0 < β := ENNReal.toReal_pos (measure_ball_pos volume _ (by linarith)).ne'
    measure_ball_lt_top.ne
  have hV : volume (ball (0 : V n) (r / 2)) = ENNReal.ofReal β :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  refine ⟨(1 + 16 / r ^ 2) / β, by positivity, fun p u hu => ?_⟩
  set I := ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) with hIdef
  by_cases hI : I = ⊤
  · rw [hI, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']; exact le_top
  set J := I.toReal with hJ
  have hI' : I = ENNReal.ofReal J := (ENNReal.ofReal_toReal hI).symm
  have hx : ∀ x ∈ ball p (r / 2), ‖u x‖ ^ 2 ≤ J / β := by
    intro x hx
    have hsub : ball x (r / 2) ⊆ ball p r := by
      apply ball_subset_ball'
      rw [mem_ball] at hx; linarith
    have h2 := (l2ball_sq_mul_vol_le u (hu.mono hsub)).trans (lintegral_mono_set hsub)
    rw [hV, ← ENNReal.ofReal_mul (sq_nonneg _), ← hIdef, hI'] at h2
    rw [le_div_iff₀ hβ]
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 h2
  set M := Real.sqrt (J / β) with hMdef
  have hJβ : 0 ≤ J / β := div_nonneg ENNReal.toReal_nonneg hβ.le
  have hMx : ∀ x ∈ ball p (r / 2), ‖u x‖ ≤ M := by
    intro x hx'
    have := Real.sqrt_le_sqrt (hx x hx')
    rwa [Real.sqrt_sq (norm_nonneg _)] at this
  have hD := norm_fderiv_le_of_ball (ρ := r / 4) (by positivity) (by linarith) u
    (hu.mono (ball_subset_ball (by linarith))) hMx
  have hD2 : ‖fderiv ℂ u p‖ ^ 2 ≤ 16 / r ^ 2 * (J / β) := by
    have := pow_le_pow_left₀ (norm_nonneg _) hD 2
    refine this.trans (le_of_eq ?_)
    rw [div_pow, Real.sq_sqrt hJβ]; field_simp; ring
  have hp := hx p (mem_ball_self (by linarith))
  rw [hI', ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2 ≤ J / β + 16 / r ^ 2 * (J / β) := add_le_add hp hD2
    _ = (1 + 16 / r ^ 2) / β * J := by ring

end

end GlobalTheory
