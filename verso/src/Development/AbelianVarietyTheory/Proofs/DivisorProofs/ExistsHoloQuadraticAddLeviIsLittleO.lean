import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.RegMaxA
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.TaylorLevi

/- English proof (translation)
Use `set D := fderiv ℝ φ p`. Use `set B := fderiv ℝ (fderiv ℝ φ) p`. Establish `hB : HasFDerivAt (fderiv ℝ φ) B p` using `((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt`. Establish `hsymm : ∀ u w, B u w = B w u` using `fun u w => (hφ.isSymmSndFDerivAt (by simp [minSmoothness])) u w`. Establish `hdiff` using `eventually_differentiableAt_of_contDiffAt hφ`.

Establish `hlo` using `hB.isLittleO`. Use `set g : E → ℝ := fun w => φ w - D (w - p) - 1 / 2 * B (w - p) (w - p)`. Establish `hg : ∀ w, DifferentiableAt ℝ φ w → HasFDerivAt g (fderiv ℝ φ w - D - B (w - p)) w`. Introduce `w hw`. Establish `h1 : HasFDerivAt (fun x : E => x - p) (ContinuousLinearMap.id ℝ E) w` using `(hasFDerivAt_id w).sub_const p`.

Establish `h2 : HasFDerivAt (fun y => B (y - p) (y - p)) _ w` using `B.hasFDerivAt_of_bilinear h1 h1`. Establish `h3` using `(hw.hasFDerivAt.sub (D.hasFDerivAt.comp w h1)).sub (HasFDerivAt.const_mul h2 (1 / 2 : ℝ))`. Use `h3.congr_fderiv ?_` and prove the remaining obligations. Use extensionality with `u`. Simplify using the standard rewrite rules.

Rewrite using `[hsymm u w, hsymm u p]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Asymptotics.isLittleO_iff]`. Introduce `c hc`. Establish `h4` using `(Asymptotics.isLittleO_iff.1 hlo) hc`.

Take `⟨δ, hδ, hball⟩` from `Metric.eventually_nhds_iff_ball.1 (h4.and hdiff)`. Use `filter_upwards [Metric.ball_mem_nhds p hδ] with v hv`. Establish `hsub : closedBall p ‖v - p‖ ⊆ ball p δ`. Apply `closedBall_subset_ball` to reduce the goal to its premises. Rewrite using `[← dist_eq_norm]`.

Conclude with `mem_ball.1 hv`. Establish `hmvt` using `(convex_closedBall p ‖v - p‖).norm_image_sub_le_of_norm_hasFDerivWithin_le (f := g) (C := c * ‖v - p‖) (fun w hw => (hg w (hball w (hsub hw)).2).hasFDerivWithinAt) (fun w hw => by`. Establish `hw'` using `hball w (hsub hw)`. Establish `e1 : ‖fderiv ℝ φ w - D - B (w - p)‖ ≤ c * ‖w - p‖`. Simplify using `using hw'.1`.

Establish `e2 : ‖w - p‖ ≤ ‖v - p‖` using `by rw [← dist_eq_norm]; exact mem_closedBall.1 hw`. Conclude with `e1.trans (mul_le_mul_of_nonneg_left e2 hc.le))`. Use the proof step `(mem_closedBall_self (norm_nonneg _)) (by rw [mem_closedBall, dist_eq_norm])`. Establish `: g v - g p = φ v - φ p - D (v - p) - B (v - p) (v - p) / 2`. Simplify using `only [g]`.

Rewrite using `[sub_self]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite `hmvt` using `[this]`. Rewrite using `[norm_pow, norm_norm]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem taylor_two {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : E → ℝ) (p : E)
    (hφ : ContDiffAt ℝ 2 φ p) :
    (fun v => φ v - φ p - fderiv ℝ φ p (v - p) - fderiv ℝ (fderiv ℝ φ) p (v - p) (v - p) / 2)
      =o[𝓝 p] (fun v => ‖v - p‖ ^ 2) := by
  set D := fderiv ℝ φ p
  set B := fderiv ℝ (fderiv ℝ φ) p
  have hB : HasFDerivAt (fderiv ℝ φ) B p :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hsymm : ∀ u w, B u w = B w u := fun u w =>
    (hφ.isSymmSndFDerivAt (by simp [minSmoothness])) u w
  have hdiff := eventually_differentiableAt_of_contDiffAt hφ
  have hlo := hB.isLittleO
  set g : E → ℝ := fun w => φ w - D (w - p) - 1 / 2 * B (w - p) (w - p)
  have hg : ∀ w, DifferentiableAt ℝ φ w → HasFDerivAt g (fderiv ℝ φ w - D - B (w - p)) w := by
    intro w hw
    have h1 : HasFDerivAt (fun x : E => x - p) (ContinuousLinearMap.id ℝ E) w :=
      (hasFDerivAt_id w).sub_const p
    have h2 : HasFDerivAt (fun y => B (y - p) (y - p)) _ w := B.hasFDerivAt_of_bilinear h1 h1
    have h3 := (hw.hasFDerivAt.sub (D.hasFDerivAt.comp w h1)).sub (HasFDerivAt.const_mul h2 (1 / 2 : ℝ))
    refine h3.congr_fderiv ?_
    ext u
    simp
    rw [hsymm u w, hsymm u p]
    ring
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have h4 := (Asymptotics.isLittleO_iff.1 hlo) hc
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h4.and hdiff)
  filter_upwards [Metric.ball_mem_nhds p hδ] with v hv
  have hsub : closedBall p ‖v - p‖ ⊆ ball p δ := by
    apply closedBall_subset_ball
    rw [← dist_eq_norm]; exact mem_ball.1 hv
  have hmvt := (convex_closedBall p ‖v - p‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := g) (C := c * ‖v - p‖)
    (fun w hw => (hg w (hball w (hsub hw)).2).hasFDerivWithinAt)
    (fun w hw => by
      have hw' := hball w (hsub hw)
      have e1 : ‖fderiv ℝ φ w - D - B (w - p)‖ ≤ c * ‖w - p‖ := by
        simpa using hw'.1
      have e2 : ‖w - p‖ ≤ ‖v - p‖ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hw
      exact e1.trans (mul_le_mul_of_nonneg_left e2 hc.le))
    (mem_closedBall_self (norm_nonneg _)) (by rw [mem_closedBall, dist_eq_norm])
  have : g v - g p = φ v - φ p - D (v - p) - B (v - p) (v - p) / 2 := by
    simp only [g]; rw [sub_self]; simp; ring
  rw [this] at hmvt
  rw [norm_pow, norm_norm]
  calc _ ≤ c * ‖v - p‖ * ‖v - p‖ := hmvt
    _ = c * ‖v - p‖ ^ 2 := by ring

end GlobalTheory.TaylorLevi

namespace GlobalTheory.TaylorLevi

variable {n : ℕ}

noncomputable section

/- English proof (translation)
Use extensionality with `i`. Simplify using `[rmVec, bas, EuclideanSpace.single_apply, Pi.single_apply]`.
-/
theorem rmVec_coord (h : V n) : rmVec (fun j => h j) = h := by
  ext i
  simp [rmVec, bas, EuclideanSpace.single_apply, Pi.single_apply]

def linCoef (D : V n →L[ℝ] ℝ) (j : Fin n) : ℂ :=
  (D (bas n j) : ℂ) - Complex.I * (D (Complex.I • bas n j) : ℂ)

def quadCoef (B : V n →L[ℝ] V n →L[ℝ] ℝ) (j k : Fin n) : ℂ :=
  ((B (bas n j) (bas n k) - B (Complex.I • bas n j) (Complex.I • bas n k) : ℝ) : ℂ)
    - Complex.I * ((B (Complex.I • bas n j) (bas n k) + B (bas n j) (Complex.I • bas n k) : ℝ) : ℂ)

/- English proof (translation)
Simplify using `only [rmVec, map_sum, Complex.re_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[rm_cplx_smul_eq]`. Simplify using `[linCoef, Complex.mul_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lin_re (D : V n →L[ℝ] ℝ) (ξ : Fin n → ℂ) :
    (∑ j, linCoef D j * ξ j).re = D (rmVec ξ) := by
  simp only [rmVec, map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rm_cplx_smul_eq]
  simp [linCoef, Complex.mul_re]
  ring

/- English proof (translation)
Rewrite using `[rm_I_smul_vec, rmVec, rm_bil_sum, rm_bil_sum, Complex.re_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.re_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[rm_bil_expand B (ξ j) (ξ k), rm_bil_expand B (Complex.I * ξ j) (Complex.I * ξ k)]`.

Simplify using `[quadCoef, Complex.mul_re, Complex.mul_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_re (B : V n →L[ℝ] V n →L[ℝ] ℝ) (ξ : Fin n → ℂ) :
    (∑ j, ∑ k, quadCoef B j k * ξ j * ξ k).re =
      B (rmVec ξ) (rmVec ξ) - B (Complex.I • rmVec ξ) (Complex.I • rmVec ξ) := by
  rw [rm_I_smul_vec, rmVec, rm_bil_sum, rm_bil_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rm_bil_expand B (ξ j) (ξ k), rm_bil_expand B (Complex.I * ξ j) (Complex.I * ξ k)]
  simp [quadCoef, Complex.mul_re, Complex.mul_im]
  ring

end

end GlobalTheory.TaylorLevi

namespace GlobalTheory.TaylorLevi

/- English proof (translation)
Introduce `n φ p hφ`. Use `set D := fderiv ℝ φ p`. Use `set B := fderiv ℝ (fderiv ℝ φ) p`. Use `⟨fun v => (φ p : ℂ) / 2 + (∑ j, linCoef D j * (v - p) j) / 2 + (∑ j, ∑ k, quadCoef B j k * (v - p) j * (v - p) k) / 8, ?_, ?_⟩` and prove the remaining obligations. Establish `hc : ∀ j, Differentiable ℂ (fun v : V n => (v - p) j)` using `fun j => (EuclideanSpace.proj j : V n →L[ℂ] ℂ).differentiable.comp (differentiable_id.sub_const p) fun_prop`.

Use `(taylor_two φ p hφ).congr' ?_ (EventuallyEq.refl _ _) filter_upwards with v` and prove the remaining obligations. Establish `hL` using `rm_levi_re_ofReal φ p hφ (fun j => (v - p) j)`. Establish `hA` using `lin_re D (fun j => (v - p) j)`. Establish `hQ` using `quad_re B (fun j => (v - p) j)`. Rewrite `hL`, `hA`, `hQ` using `[rmVec_coord]`.

Establish `hq : ((φ p : ℂ) / 2 + (∑ j, linCoef D j * (v - p) j) / 2 + (∑ j, ∑ k, quadCoef B j k * (v - p) j * (v - p) k) / 8).re = φ p / 2 + (∑ j, linCoef D j * (v - p) j).re / 2 + (∑ j, ∑ k, quadCoef B j k * (v - p) j * (v - p) k).re / 8`. Simplify using `only [Complex.add_re, Complex.div_ofNat_re, Complex.ofReal_re]`. Rewrite using `[hq, hA, hQ]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_holo_quadratic_add_levi : ∀ (n : ℕ) (φ : V n → ℝ) (p : V n), ContDiffAt ℝ 2 φ p →
    ∃ q : V n → ℂ, Differentiable ℂ q ∧
      (fun v : V n => φ v - 2 * (q v).re
        - (leviV n (fun w => ((φ w : ℝ) : ℂ)) p (fun j => (v - p) j)).re)
        =o[𝓝 p] (fun v : V n => ‖v - p‖ ^ 2) := by
  intro n φ p hφ
  set D := fderiv ℝ φ p
  set B := fderiv ℝ (fderiv ℝ φ) p
  refine ⟨fun v => (φ p : ℂ) / 2 + (∑ j, linCoef D j * (v - p) j) / 2
      + (∑ j, ∑ k, quadCoef B j k * (v - p) j * (v - p) k) / 8, ?_, ?_⟩
  · have hc : ∀ j, Differentiable ℂ (fun v : V n => (v - p) j) := fun j =>
      (EuclideanSpace.proj j : V n →L[ℂ] ℂ).differentiable.comp (differentiable_id.sub_const p)
    fun_prop
  · refine (taylor_two φ p hφ).congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards with v
    have hL := rm_levi_re_ofReal φ p hφ (fun j => (v - p) j)
    have hA := lin_re D (fun j => (v - p) j)
    have hQ := quad_re B (fun j => (v - p) j)
    rw [rmVec_coord] at hL hA hQ
    have hq : ((φ p : ℂ) / 2 + (∑ j, linCoef D j * (v - p) j) / 2
        + (∑ j, ∑ k, quadCoef B j k * (v - p) j * (v - p) k) / 8).re
        = φ p / 2 + (∑ j, linCoef D j * (v - p) j).re / 2
          + (∑ j, ∑ k, quadCoef B j k * (v - p) j * (v - p) k).re / 8 := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.ofReal_re]
    rw [hq, hA, hQ]
    linarith

end GlobalTheory.TaylorLevi
