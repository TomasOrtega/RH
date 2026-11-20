import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableExpNegMulAbs

open MeasureTheory Filter Set
open scoped Topology FourierTransform

namespace GlobalTheory

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs`. Consider the case `exact _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs`. Consider the case `(apply _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs ..)`.
-/
theorem integrable_exp_neg_mul_abs_line {c : ℝ} (hc : 0 < c) :
    Integrable (fun s : ℝ => Real.exp (-(c * |s|))) := by
  first
  | exact @_root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs
  | exact _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs
  | (apply _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs ..)

/- English proof (translation)
Introduce and unpack `φ R hφ ⟨A, e, he, hb⟩ hz`. Use `set U : Set ℂ := {z | -(e / 2) < z.im} ∩ {z | z.im < e / 2} with hUdef`. Establish `hUo : IsOpen U` using `(isOpen_lt continuous_const Complex.continuous_im).inter (isOpen_lt Complex.continuous_im continuous_const)`. Establish `hUc : Convex ℝ U` using `(convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)`. Establish `hre : ∀ x : ℝ, (x : ℂ) ∈ U` using `fun x => by`.

Simplify using `only [hUdef, mem_inter_iff, mem_setOf_eq, Complex.ofReal_im]`. Apply the tactic sequence `constructor <;> linarith`. Establish `hint : Integrable (fun s : ℝ => A * Real.exp (-(e / 2 * |s|)))` using `(integrable_exp_neg_mul_abs_line (half_pos he)).const_mul A`. Establish `hA : 0 ≤ A`. Use `(norm_nonneg _).trans (hb 0)` as an intermediate fact.

Simplify using `using this`. Establish `hbound : ∀ s : ℝ, ∀ y ∈ U, ‖Complex.exp (-(Complex.I * y * s)) * φ s‖ ≤ A * Real.exp (-(e / 2 * |s|))`. Introduce `s y hy`. Establish `hy' : |y.im| ≤ e / 2` using `abs_le.2 ⟨hy.1.le, hy.2.le⟩`. Establish `h1 : (-(Complex.I * y * s)).re = y.im * s` using `by simp`.

Establish `h2 : y.im * s ≤ e / 2 * |s|`. Use `(le_abs_self _).trans ?_` and prove the remaining obligations. Rewrite using `[abs_mul]`. Conclude with `mul_le_mul_of_nonneg_right hy' (abs_nonneg _)`. Rewrite using `[norm_mul, Complex.norm_exp, h1]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_left_comm, ← Real.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `hdiff` using `(differentiableOn_integral_of_holomorphic_of_locally_dominated (μ := (volume : Measure ℝ)) (F := fun (s : ℝ) (y : ℂ) => Complex.exp (-(Complex.I * y * s)) * φ s) hUo (fun y _ => Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun s => Differentiable.different …`.

Establish `han` using `hdiff.analyticOnNhd hUo`. Establish `hfr : ∃ᶠ y in 𝓝[≠] (R : ℂ), ∫ s : ℝ, Complex.exp (-(Complex.I * y * s)) * φ s = 0`. Establish `ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] R) (𝓝[≠] (R : ℂ))`. Use `tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `(Complex.continuous_ofReal.tendsto R).mono_left nhdsWithin_le_nhds`.

Use `filter_upwards [self_mem_nhdsWithin] with x hx`. Simplify using `using (ne_of_gt hx)`. Use `ht.frequently (Eventually.frequently ?_)` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with x hx`. Conclude with `hz x (le_of_lt hx)`.

Establish `hzero` using `han.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc.isPreconnected (hre R) hfr`. Establish `hF : 𝓕 φ = 0`. Use function extensionality and compare the values at `w`. Rewrite using `[Real.fourier_real_eq_integral_exp_smul]`. Use `hzero (hre (2 * Real.pi * w))` as an intermediate fact.

Simplify using `only [Pi.zero_apply] at this ⊢`. Rewrite using `[← this]`. Use `integral_congr_ae (Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hφi : Integrable φ` using `((integrable_exp_neg_mul_abs_line he).const_mul A).mono' hφ.aestronglyMeasurable (Eventually.of_forall hb)`. Establish `hinv` using `hφ.fourierInv_fourier_eq hφi (by rw [hF]; exact integrable_zero _ _ _)`. Rewrite using `[← hinv, hF]`.

Use function extensionality and compare the values at `x`. Simplify using `[Real.fourierInv_eq]`.
-/
theorem eq_zero_of_exp_decay_of_fourier_eq_zero_on_halfLine :
    ∀ (φ : ℝ → ℂ) (R : ℝ), Continuous φ →
      (∃ A e : ℝ, 0 < e ∧ ∀ s, ‖φ s‖ ≤ A * Real.exp (-(e * |s|))) →
      (∀ ξ : ℝ, R ≤ ξ → ∫ s : ℝ, Complex.exp (-(Complex.I * ξ * s)) * φ s = 0) → φ = 0 := by
  rintro φ R hφ ⟨A, e, he, hb⟩ hz
  set U : Set ℂ := {z | -(e / 2) < z.im} ∩ {z | z.im < e / 2} with hUdef
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hUc : Convex ℝ U := (convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)
  have hre : ∀ x : ℝ, (x : ℂ) ∈ U := fun x => by
    simp only [hUdef, mem_inter_iff, mem_setOf_eq, Complex.ofReal_im]
    constructor <;> linarith
  have hint : Integrable (fun s : ℝ => A * Real.exp (-(e / 2 * |s|))) :=
    (integrable_exp_neg_mul_abs_line (half_pos he)).const_mul A
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hb 0)
    simpa using this
  have hbound : ∀ s : ℝ, ∀ y ∈ U,
      ‖Complex.exp (-(Complex.I * y * s)) * φ s‖ ≤ A * Real.exp (-(e / 2 * |s|)) := by
    intro s y hy
    have hy' : |y.im| ≤ e / 2 := abs_le.2 ⟨hy.1.le, hy.2.le⟩
    have h1 : (-(Complex.I * y * s)).re = y.im * s := by simp
    have h2 : y.im * s ≤ e / 2 * |s| := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hy' (abs_nonneg _)
    rw [norm_mul, Complex.norm_exp, h1]
    calc Real.exp (y.im * s) * ‖φ s‖
        ≤ Real.exp (e / 2 * |s|) * (A * Real.exp (-(e * |s|))) :=
          mul_le_mul (Real.exp_le_exp.2 h2) (hb s) (norm_nonneg _) (Real.exp_pos _).le
      _ = A * Real.exp (-(e / 2 * |s|)) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
  have hdiff := (differentiableOn_integral_of_holomorphic_of_locally_dominated
    (μ := (volume : Measure ℝ))
    (F := fun (s : ℝ) (y : ℂ) => Complex.exp (-(Complex.I * y * s)) * φ s) hUo
    (fun y _ => Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun s => Differentiable.differentiableOn (by fun_prop))
    (fun x hx => ⟨U, hUo.mem_nhds hx, _, hint, Eventually.of_forall hbound⟩)).1
  have han := hdiff.analyticOnNhd hUo
  have hfr : ∃ᶠ y in 𝓝[≠] (R : ℂ),
      ∫ s : ℝ, Complex.exp (-(Complex.I * y * s)) * φ s = 0 := by
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] R) (𝓝[≠] (R : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto R).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using (ne_of_gt hx)
    refine ht.frequently (Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hz x (le_of_lt hx)
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc.isPreconnected
    (hre R) hfr
  have hF : 𝓕 φ = 0 := by
    funext w
    rw [Real.fourier_real_eq_integral_exp_smul]
    have := hzero (hre (2 * Real.pi * w))
    simp only [Pi.zero_apply] at this ⊢
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [smul_eq_mul]
    congr 2
    push_cast
    ring
  have hφi : Integrable φ :=
    ((integrable_exp_neg_mul_abs_line he).const_mul A).mono' hφ.aestronglyMeasurable
      (Eventually.of_forall hb)
  have hinv := hφ.fourierInv_fourier_eq hφi (by rw [hF]; exact integrable_zero _ _ _)
  rw [← hinv, hF]
  funext x
  simp [Real.fourierInv_eq]

end GlobalTheory
