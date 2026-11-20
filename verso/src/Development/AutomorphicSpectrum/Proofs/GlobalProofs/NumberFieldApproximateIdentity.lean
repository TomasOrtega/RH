import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfReal

noncomputable def bumpLine : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/- English proof (translation)
Apply `ContDiffBump.zero_of_le_dist` to reduce the goal to its premises. Simplify `hy` using `[bumpLine, Real.dist_eq]`.
-/
theorem bumpLine_eq_zero {y : ℝ} (hy : 1 ≤ |y|) : bumpLine y = 0 := by
  apply ContDiffBump.zero_of_le_dist
  simpa [bumpLine, Real.dist_eq] using hy

/- English proof (translation)
Rewrite using `[Measure.integral_comp_mul_left (fun y => bumpLine y) c]`. Establish `h : 0 < ∫ y : ℝ, bumpLine y` using `bumpLine.integral_pos`. Establish `: 0 < |c⁻¹|` using `abs_pos.mpr (inv_ne_zero hc.ne')`. Simplify using `using mul_pos this h`.
-/
theorem integral_bumpLine_scaled_pos {c : ℝ} (hc : 0 < c) :
    0 < ∫ y : ℝ, bumpLine (c * y) := by
  rw [Measure.integral_comp_mul_left (fun y => bumpLine y) c]
  have h : 0 < ∫ y : ℝ, bumpLine y := bumpLine.integral_pos
  have : 0 < |c⁻¹| := abs_pos.mpr (inv_ne_zero hc.ne')
  simpa using mul_pos this h

/- English proof (translation)
Establish `hsm : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => ((bumpLine (c * y) : ℝ) : ℂ))` using `Complex.ofRealCLM.contDiff.comp (bumpLine.contDiff.comp (contDiff_const.mul contDiff_id))`. Establish `hcs : HasCompactSupport (fun y : ℝ => ((bumpLine (c * y) : ℝ) : ℂ))`. Apply `HasCompactSupport.intro (K := Metric.closedBall 0 (1 / c)) (isCompact_closedBall _ _)` to reduce the goal to its premises. Introduce `y hy`. Establish `h1 : 1 / c < |y|` using `by simpa [Real.dist_eq] using hy`.

Establish `h2 : 1 ≤ |c * y|`. Rewrite using `[abs_mul, abs_of_pos hc]`. Rewrite `h1` using `[div_lt_iff₀ hc]`. Use the polynomial consequences of the given equalities and inequalities. Simplify using `[bumpLine_eq_zero h2]`.

Set `S : SchwartzMap ℝ ℂ` to `hcs.toSchwartzMap hsm`. Establish `hI : Integrable (fun u : ℝ => (FourierTransform.fourier S) u)` using `(FourierTransform.fourier S).integrable`. Establish `hI2` using `hI.comp_mul_left' (neg_ne_zero.mpr ha)`. Use `hI2.congr (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Simplify using `only [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Establish `hS : S y = ((bumpLine (c * y) : ℝ) : ℂ)` using `rfl`. Simplify using `only [hS, smul_eq_mul]`. Rewrite using `[mul_comm]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integrable_osc_line {c a : ℝ} (hc : 0 < c) (ha : a ≠ 0) :
    Integrable (fun s : ℝ => ∫ y : ℝ, ((bumpLine (c * y) : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((a * (y * s) : ℝ) : ℂ))) := by
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => ((bumpLine (c * y) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (bumpLine.contDiff.comp (contDiff_const.mul contDiff_id))
  have hcs : HasCompactSupport (fun y : ℝ => ((bumpLine (c * y) : ℝ) : ℂ)) := by
    apply HasCompactSupport.intro (K := Metric.closedBall 0 (1 / c)) (isCompact_closedBall _ _)
    intro y hy
    have h1 : 1 / c < |y| := by simpa [Real.dist_eq] using hy
    have h2 : 1 ≤ |c * y| := by
      rw [abs_mul, abs_of_pos hc]
      rw [div_lt_iff₀ hc] at h1
      nlinarith
    simp [bumpLine_eq_zero h2]
  let S : SchwartzMap ℝ ℂ := hcs.toSchwartzMap hsm
  have hI : Integrable (fun u : ℝ => (FourierTransform.fourier S) u) :=
    (FourierTransform.fourier S).integrable
  have hI2 := hI.comp_mul_left' (neg_ne_zero.mpr ha)
  refine hI2.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hS : S y = ((bumpLine (c * y) : ℝ) : ℂ) := rfl
  simp only [hS, smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

/- English proof (translation)
Establish `hpos : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1` using `fun k => by positivity`. Establish `hts : ∀ k : ℕ, tsupport (fun x : P → ℝ => ∏ w, bumpLine (((k : ℝ) + 1) * x w)) ⊆ Metric.closedBall 0 (1 / ((k : ℝ) + 1))`. Introduce `k`. Apply `closure_minimal _ Metric.isClosed_closedBall` to reduce the goal to its premises. Introduce `x hx`.

Rewrite using `[Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by have := hpos k; positivity)]`. Introduce `w`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Apply `hx` to reduce the goal to its premises.

Apply `Finset.prod_eq_zero (Finset.mem_univ w)` to reduce the goal to its premises. Apply `bumpLine_eq_zero` to reduce the goal to its premises. Rewrite using `[abs_mul, abs_of_pos (hpos k)]`. Rewrite `hlt` using `[Real.norm_eq_abs, div_lt_iff₀ (hpos k)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨fun k x => ∏ w, bumpLine (((k : ℝ) + 1) * x w), fun k => ⟨?_, ?_, ?_, ?_⟩, hts, fun k => ?_⟩` and prove the remaining obligations. Conclude with `continuous_finset_prod _ fun w _ => bumpLine.continuous.comp (continuous_const.mul (continuous_apply w))`. Conclude with `(isCompact_closedBall (0 : P → ℝ) _).of_isClosed_subset (isClosed_tsupport _) (hts k)`. Conclude with `fun x => Finset.prod_nonneg fun w _ => bumpLine.nonneg`. Rewrite using `[integral_fintype_prod_volume_eq_prod (fun _ (y : ℝ) => bumpLine (((k : ℝ) + 1) * y))]`.

Conclude with `Finset.prod_pos fun w _ => integral_bumpLine_scaled_pos (hpos k)`. Establish `hI` using `Integrable.fintype_prod (f := fun (w : P) (s : ℝ) => ∫ y : ℝ, ((bumpLine (((k : ℝ) + 1) * y) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((a w * (y * s) : ℝ) : ℂ))) (fun w => integrable_osc_line (hpos k) (ha w))`. Use `hI.congr (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← integral_fintype_prod_volume_eq_prod (fun (w : P) (y : ℝ) => ((bumpLine (((k : ℝ) + 1) * y) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((a w * (y * t w) : ℝ) : ℂ)))]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Finset.prod_mul_distrib]`. Use `push_cast`. Rewrite using `[Finset.mul_sum, Complex.exp_sum]`.
-/
theorem exists_bumps (P : Type) [Fintype P] (a : P → ℝ) (ha : ∀ w, a w ≠ 0) :
    ∃ g : ℕ → (P → ℝ) → ℝ, (∀ k, Continuous (g k) ∧ HasCompactSupport (g k) ∧ (∀ x, 0 ≤ g k x) ∧ 0 < ∫ x, g k x) ∧ (∀ k, tsupport (g k) ⊆ Metric.closedBall 0 (1 / ((k : ℝ) + 1))) ∧ ∀ k, Integrable (fun t : P → ℝ => ∫ x, (g k x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * t w) : ℝ) : ℂ))) := by
  classical
  have hpos : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hts : ∀ k : ℕ, tsupport (fun x : P → ℝ => ∏ w, bumpLine (((k : ℝ) + 1) * x w)) ⊆
      Metric.closedBall 0 (1 / ((k : ℝ) + 1)) := by
    intro k
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by have := hpos k; positivity)]
    intro w
    by_contra hlt
    push_neg at hlt
    apply hx
    apply Finset.prod_eq_zero (Finset.mem_univ w)
    apply bumpLine_eq_zero
    rw [abs_mul, abs_of_pos (hpos k)]
    rw [Real.norm_eq_abs, div_lt_iff₀ (hpos k)] at hlt
    linarith
  refine ⟨fun k x => ∏ w, bumpLine (((k : ℝ) + 1) * x w), fun k => ⟨?_, ?_, ?_, ?_⟩, hts, fun k => ?_⟩
  · exact continuous_finset_prod _ fun w _ =>
      bumpLine.continuous.comp (continuous_const.mul (continuous_apply w))
  · exact (isCompact_closedBall (0 : P → ℝ) _).of_isClosed_subset (isClosed_tsupport _) (hts k)
  · exact fun x => Finset.prod_nonneg fun w _ => bumpLine.nonneg
  · rw [integral_fintype_prod_volume_eq_prod (fun _ (y : ℝ) => bumpLine (((k : ℝ) + 1) * y))]
    exact Finset.prod_pos fun w _ => integral_bumpLine_scaled_pos (hpos k)
  · have hI := Integrable.fintype_prod (f := fun (w : P) (s : ℝ) => ∫ y : ℝ,
      ((bumpLine (((k : ℝ) + 1) * y) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((a w * (y * s) : ℝ) : ℂ)))
      (fun w => integrable_osc_line (hpos k) (ha w))
    refine hI.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [← integral_fintype_prod_volume_eq_prod (fun (w : P) (y : ℝ) =>
      ((bumpLine (((k : ℝ) + 1) * y) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((a w * (y * t w) : ℝ) : ℂ)))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [Finset.prod_mul_distrib]
    push_cast
    rw [Finset.mul_sum, Complex.exp_sum]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfReal
