import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial MeasureTheory Finset
open scoped InnerProductSpace

noncomputable section

namespace FibreConstantClosedForm

/- English proof (translation)
Rewrite using `[eval_eq']`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Simplify using `[Fin.prod_univ_two]`.
-/
theorem eval_two (g : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
    eval ![x, y] g = ∑ d ∈ g.support, g.coeff d * (x ^ d 0 * y ^ d 1) := by
  rw [eval_eq']
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [Fin.prod_univ_two]

/- English proof (translation)
Establish `h1 : ‖(n : E3)‖ = 1` using `mem_sphere_zero_iff_norm.mp n.2`. Establish `h2` using `PiLp.norm_apply_le (n : E3) 2`. Rewrite `h2` using `[h1, Real.norm_eq_abs]`. Conclude with `h2`.
-/
theorem abs_height_le (n : Sphere2) : |height n| ≤ 1 := by
  have h1 : ‖(n : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp n.2
  have h2 := PiLp.norm_apply_le (n : E3) 2
  rw [h1, Real.norm_eq_abs] at h2
  exact h2

/- English proof (translation)
Unfold `height`. Use `fun_prop`.
-/
theorem continuous_height : Continuous height := by
  unfold height
  fun_prop

/- English proof (translation)
Simplify using `[centredPrimitive]`.
-/
theorem centredPrimitive_X_pow (a : ℕ) (c : ℝ) :
    centredPrimitive (Polynomial.X ^ a) c =
      ∫ t in (-1 : ℝ)..c, (t ^ a - uniformMean (fun t : ℝ => t ^ a)) := by
  simp [centredPrimitive]

/- English proof (translation)
Assume the negation of the conclusion as `hni`. Establish `h` using `h0.1 1 1`. Establish `hm : uniformMean (fun _ : ℝ => (1 : ℝ)) = 1`. Rewrite using `[uniformMean, intervalIntegral.integral_const]`. Evaluate the numerical expressions.

Establish `hc : ∀ c, centredPrimitive 1 c = 0`. Introduce `c`. Simplify using `only [centredPrimitive, Polynomial.eval_one, hm, sub_self, intervalIntegral.integral_zero]`. Simplify using `only [Polynomial.eval_one, mul_one, hm, hc, zero_mul, zero_div, intervalIntegral.integral_zero] at h`. Rewrite `h` using `[integral_undef hni]`.

Evaluate the numerical expressions using `at h`.
-/
theorem integrable_kernel (h0 : ZonalBilinearFormula.Statement) :
    Integrable (fun p : Sphere2 × Sphere2 => kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ) pairMeasure := by
  by_contra hni
  have h := h0.1 1 1
  have hm : uniformMean (fun _ : ℝ => (1 : ℝ)) = 1 := by
    rw [uniformMean, intervalIntegral.integral_const]
    norm_num
  have hc : ∀ c, centredPrimitive 1 c = 0 := by
    intro c
    simp only [centredPrimitive, Polynomial.eval_one, hm, sub_self, intervalIntegral.integral_zero]
  simp only [Polynomial.eval_one, mul_one, hm, hc, zero_mul, zero_div,
    intervalIntegral.integral_zero] at h
  rw [integral_undef hni] at h
  norm_num at h

/- English proof (translation)
Use `(integrable_kernel h0).mul_bdd (c := 1) ?_ (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Conclude with `(((continuous_height.comp continuous_fst).pow a).mul ((continuous_height.comp continuous_snd).pow b)).aestronglyMeasurable`. Rewrite using `[norm_mul, norm_pow, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]`. Conclude with `mul_le_one₀ (pow_le_one₀ (abs_nonneg _) (abs_height_le _)) (by positivity) (pow_le_one₀ (abs_nonneg _) (abs_height_le _))`.
-/
theorem integrable_term (h0 : ZonalBilinearFormula.Statement) (a b : ℕ) :
    Integrable (fun p : Sphere2 × Sphere2 =>
      kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * (height p.1 ^ a * height p.2 ^ b)) pairMeasure := by
  refine (integrable_kernel h0).mul_bdd (c := 1) ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact (((continuous_height.comp continuous_fst).pow a).mul
      ((continuous_height.comp continuous_snd).pow b)).aestronglyMeasurable
  · rw [norm_mul, norm_pow, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_one₀ (pow_le_one₀ (abs_nonneg _) (abs_height_le _)) (by positivity)
      (pow_le_one₀ (abs_nonneg _) (abs_height_le _))

/- English proof (translation)
Establish `h` using `h0.1 (Polynomial.X ^ a) (Polynomial.X ^ b)`. Simplify using `only [Polynomial.eval_pow, Polynomial.eval_X] at h`. Rewrite using `[← h]`. Use `congr 1`. Use function extensionality and compare the values at `p`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem term_eq (h0 : ZonalBilinearFormula.Statement) (a b : ℕ) :
    ∫ p, kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * (height p.1 ^ a * height p.2 ^ b) ∂pairMeasure =
      -(1 / 2) * uniformMean (fun t : ℝ => t ^ a) * uniformMean (fun t : ℝ => t ^ b) -
        (1 / 4) * ∫ c in (-1 : ℝ)..1,
          centredPrimitive (Polynomial.X ^ a) c * centredPrimitive (Polynomial.X ^ b) c /
            (1 - c ^ 2) := by
  have h := h0.1 (Polynomial.X ^ a) (Polynomial.X ^ b)
  simp only [Polynomial.eval_pow, Polynomial.eval_X] at h
  rw [← h]
  congr 1
  funext p
  ring

/- English proof (translation)
Establish `hfun : (fun p : Sphere2 × Sphere2 => kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * eval ![height p.1, height p.2] g) = fun p => ∑ d ∈ g.support, g.coeff d * (kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * (height p.1 ^ d 0 * height p.2 ^ d 1))`. Use function extensionality and compare the values at `p`. Rewrite using `[eval_two, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hfun, integral_finsetSum _ (fun d _ => (integrable_term h0 _ _).const_mul (g.coeff d))]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[integral_const_mul]`.
-/
theorem integral_expand (h0 : ZonalBilinearFormula.Statement) (g : MvPolynomial (Fin 2) ℝ) :
    ∫ p, kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * eval ![height p.1, height p.2] g ∂pairMeasure =
      ∑ d ∈ g.support, g.coeff d * ∫ p, kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ *
        (height p.1 ^ d 0 * height p.2 ^ d 1) ∂pairMeasure := by
  have hfun : (fun p : Sphere2 × Sphere2 =>
      kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * eval ![height p.1, height p.2] g) =
      fun p => ∑ d ∈ g.support, g.coeff d * (kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ *
        (height p.1 ^ d 0 * height p.2 ^ d 1)) := by
    funext p
    rw [eval_two, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [hfun, integral_finsetSum _ (fun d _ => (integrable_term h0 _ _).const_mul (g.coeff d))]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [integral_const_mul]

/- English proof (translation)
The claim follows from `intervalIntegral.integral_finsetSum fun i hi => (hf i hi).intervalIntegrable a b`.
-/
theorem isum {ι : Type*} (a b : ℝ) (s : Finset ι) (f : ι → ℝ → ℝ) (hf : ∀ i ∈ s, Continuous (f i)) :
    ∫ x in a..b, ∑ i ∈ s, f i x = ∑ i ∈ s, ∫ x in a..b, f i x :=
  intervalIntegral.integral_finsetSum fun i hi => (hf i hi).intervalIntegrable a b

/- English proof (translation)
Repeatedly rewrite using `[eval_two]`. Rewrite using `[isum _ _ _ _ (fun d _ => by fun_prop)]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[← intervalIntegral.integral_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `y`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_snd (g : MvPolynomial (Fin 2) ℝ) (x : ℝ) :
    ∫ y in (-1 : ℝ)..1, eval ![x, y] g =
      ∑ d ∈ g.support, g.coeff d * x ^ d 0 * ∫ y in (-1 : ℝ)..1, y ^ d 1 := by
  simp_rw [eval_two]
  rw [isum _ _ _ _ (fun d _ => by fun_prop)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext y
  ring

/- English proof (translation)
Repeatedly rewrite using `[eval_two]`. Rewrite using `[isum _ _ _ _ (fun d _ => by fun_prop)]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_mul_const]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_fst (g : MvPolynomial (Fin 2) ℝ) (y : ℝ) :
    ∫ x in (-1 : ℝ)..1, eval ![x, y] g =
      ∑ d ∈ g.support, g.coeff d * (∫ x in (-1 : ℝ)..1, x ^ d 0) * y ^ d 1 := by
  simp_rw [eval_two]
  rw [isum _ _ _ _ (fun d _ => by fun_prop)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_mul_const]
  congr 1
  funext x
  ring

/- English proof (translation)
Unfold `squareMean`. Repeatedly rewrite using `[integral_snd]`. Rewrite using `[isum _ _ _ _ (fun d _ => by fun_prop), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Simplify using `only [uniformMean]`.

Rewrite using `[intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem squareMean_eq (g : MvPolynomial (Fin 2) ℝ) :
    squareMean g = ∑ d ∈ g.support,
      g.coeff d * (uniformMean (fun t : ℝ => t ^ d 0) * uniformMean (fun t : ℝ => t ^ d 1)) := by
  unfold squareMean
  simp_rw [integral_snd]
  rw [isum _ _ _ _ (fun d _ => by fun_prop), Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [uniformMean]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
  ring

/- English proof (translation)
Establish `hpt : ∀ s t : ℝ, eval ![s, t] g - (1 / 2) * (∫ x in (-1 : ℝ)..1, eval ![x, t] g) - (1 / 2) * (∫ y in (-1 : ℝ)..1, eval ![s, y] g) + squareMean g = ∑ d ∈ g.support, g.coeff d * ((s ^ d 0 - uniformMean (fun t : ℝ => t ^ d 0)) * (t ^ d 1 - uniformMean (fun t : ℝ => t ^ d 1)))`. Introduce `s t`. Rewrite using `[eval_two, integral_fst, integral_snd, squareMean_eq]`. Simplify using `only [uniformMean, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `hin : ∀ s : ℝ, ∫ t in (-1 : ℝ)..c, ∑ d ∈ g.support, g.coeff d * ((s ^ d 0 - uniformMean (fun t : ℝ => t ^ d 0)) * (t ^ d 1 - uniformMean (fun t : ℝ => t ^ d 1))) = ∑ d ∈ g.support, g.coeff d * (s ^ d 0 - uniformMean (fun t : ℝ => t ^ d 0)) * centredPrimitive (Polynomial.X ^ d 1) …`. Introduce `s`. Rewrite using `[isum _ _ _ _ (fun d _ => by fun_prop)]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations.

Rewrite using `[centredPrimitive_X_pow, ← intervalIntegral.integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Expand and normalize the polynomial expressions, which then agree. Unfold `doublyCentred`.

Repeatedly rewrite using `[hpt, hin]`. Rewrite using `[isum _ _ _ _ (fun d _ => by fun_prop)]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, centredPrimitive_X_pow (d 0)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem doublyCentred_eq (g : MvPolynomial (Fin 2) ℝ) (c : ℝ) :
    doublyCentred g c = ∑ d ∈ g.support, g.coeff d *
      (centredPrimitive (Polynomial.X ^ d 0) c * centredPrimitive (Polynomial.X ^ d 1) c) := by
  have hpt : ∀ s t : ℝ, eval ![s, t] g - (1 / 2) * (∫ x in (-1 : ℝ)..1, eval ![x, t] g) -
      (1 / 2) * (∫ y in (-1 : ℝ)..1, eval ![s, y] g) + squareMean g =
      ∑ d ∈ g.support, g.coeff d * ((s ^ d 0 - uniformMean (fun t : ℝ => t ^ d 0)) *
        (t ^ d 1 - uniformMean (fun t : ℝ => t ^ d 1))) := by
    intro s t
    rw [eval_two, integral_fst, integral_snd, squareMean_eq]
    simp only [uniformMean, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  have hin : ∀ s : ℝ, ∫ t in (-1 : ℝ)..c, ∑ d ∈ g.support, g.coeff d *
      ((s ^ d 0 - uniformMean (fun t : ℝ => t ^ d 0)) *
        (t ^ d 1 - uniformMean (fun t : ℝ => t ^ d 1))) =
      ∑ d ∈ g.support, g.coeff d * (s ^ d 0 - uniformMean (fun t : ℝ => t ^ d 0)) *
        centredPrimitive (Polynomial.X ^ d 1) c := by
    intro s
    rw [isum _ _ _ _ (fun d _ => by fun_prop)]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [centredPrimitive_X_pow, ← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  unfold doublyCentred
  simp_rw [hpt, hin]
  rw [isum _ _ _ _ (fun d _ => by fun_prop)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
    centredPrimitive_X_pow (d 0)]
  ring

/- English proof (translation)
Establish `h` using `intervalIntegral.norm_integral_le_of_norm_le_const (a := -1) (b := 1) (C := 1) (f := fun t : ℝ => t ^ a) (fun x hx => ?_)`. Rewrite `h` using `[Real.norm_eq_abs]`. Rewrite using `[uniformMean, abs_mul]`. Evaluate the numerical expressions using `at h ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite `hx` using `[Set.uIoc_of_le (by norm_num)]`. Rewrite using `[Real.norm_eq_abs, abs_pow]`. Conclude with `pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨hx.1.le, hx.2⟩)`.
-/
theorem abs_uniformMean_pow_le (a : ℕ) : |uniformMean (fun t : ℝ => t ^ a)| ≤ 1 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -1) (b := 1) (C := 1)
    (f := fun t : ℝ => t ^ a) (fun x hx => ?_)
  · rw [Real.norm_eq_abs] at h
    rw [uniformMean, abs_mul]
    norm_num at h ⊢
    linarith
  · rw [Set.uIoc_of_le (by norm_num)] at hx
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨hx.1.le, hx.2⟩)

/- English proof (translation)
Establish `h1 : |x ^ a| ≤ 1`. Rewrite using `[abs_pow]`. Conclude with `pow_le_one₀ (abs_nonneg _) (abs_le.mpr hx)`. Establish `h2` using `abs_uniformMean_pow_le a`. Rewrite using `[Real.norm_eq_abs]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem abs_centred_pow_le (a : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖x ^ a - uniformMean (fun t : ℝ => t ^ a)‖ ≤ 2 := by
  have h1 : |x ^ a| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr hx)
  have h2 := abs_uniformMean_pow_le a
  rw [Real.norm_eq_abs]
  calc |x ^ a - uniformMean (fun t : ℝ => t ^ a)|
      ≤ |x ^ a| + |uniformMean (fun t : ℝ => t ^ a)| := abs_sub _ _
    _ ≤ 2 := by linarith

/- English proof (translation)
The claim follows from `|centredPrimitive (Polynomial.X ^ a) c| ≤ 2 * (c + 1) := by rw [centredPrimitive_X_pow] have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -1) (b := c) (C := 2) (f := fun t : ℝ => t ^ a - uniformMean (fun t : ℝ => t ^ a)) (fun x hx => ?_) · rw [Real.norm_eq_abs, a …`.
-/
theorem abs_centredPrimitive_le_left (a : ℕ) {c : ℝ} (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    |centredPrimitive (Polynomial.X ^ a) c| ≤ 2 * (c + 1) := by
  rw [centredPrimitive_X_pow]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -1) (b := c) (C := 2)
    (f := fun t : ℝ => t ^ a - uniformMean (fun t : ℝ => t ^ a)) (fun x hx => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hc.1] : (0 : ℝ) ≤ c - -1)] at h
    linarith
  · rw [Set.uIoc_of_le hc.1] at hx
    exact abs_centred_pow_le a ⟨hx.1.le, hx.2.trans hc.2⟩

/- English proof (translation)
Rewrite using `[intervalIntegral.integral_sub ((continuous_pow a).intervalIntegrable _ _) intervalIntegrable_const, intervalIntegral.integral_const, uniformMean]`. Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem centredPrimitive_one (a : ℕ) :
    ∫ t in (-1 : ℝ)..1, (t ^ a - uniformMean (fun t : ℝ => t ^ a)) = 0 := by
  rw [intervalIntegral.integral_sub ((continuous_pow a).intervalIntegrable _ _)
    intervalIntegrable_const, intervalIntegral.integral_const, uniformMean]
  simp only [smul_eq_mul]
  ring

/- English proof (translation)
The claim follows from `|centredPrimitive (Polynomial.X ^ a) c| ≤ 2 * (1 - c) := by have hcont : Continuous fun t : ℝ => t ^ a - uniformMean (fun t : ℝ => t ^ a) := by fun_prop have hsplit := intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable (μ := volume) (-1) c) (hcont.interval …`.
-/
theorem abs_centredPrimitive_le_right (a : ℕ) {c : ℝ} (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    |centredPrimitive (Polynomial.X ^ a) c| ≤ 2 * (1 - c) := by
  have hcont : Continuous fun t : ℝ => t ^ a - uniformMean (fun t : ℝ => t ^ a) := by fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) (-1) c) (hcont.intervalIntegrable (μ := volume) c 1)
  rw [centredPrimitive_one] at hsplit
  rw [centredPrimitive_X_pow, eq_neg_of_add_eq_zero_left hsplit, abs_neg]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := 1) (C := 2)
    (f := fun t : ℝ => t ^ a - uniformMean (fun t : ℝ => t ^ a)) (fun x hx => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hc.2] : (0 : ℝ) ≤ 1 - c)] at h
    exact h
  · rw [Set.uIoc_of_le hc.2] at hx
    exact abs_centred_pow_le a ⟨(hc.1.trans hx.1.le), hx.2⟩

/- English proof (translation)
Establish `h : centredPrimitive (Polynomial.X ^ a) = fun c => ∫ t in (-1 : ℝ)..c, (t ^ a - uniformMean (fun t : ℝ => t ^ a))`. Use function extensionality and compare the values at `(centredPrimitive_X_pow a)`. Rewrite using `[h]`. Conclude with `intervalIntegral.continuous_primitive (fun _ _ => (by fun_prop : Continuous fun t : ℝ => t ^ a - uniformMean (fun t : ℝ => t ^ a)).intervalIntegrable _ _) (-1)`.
-/
theorem continuous_centredPrimitive (a : ℕ) : Continuous (centredPrimitive (Polynomial.X ^ a)) := by
  have h : centredPrimitive (Polynomial.X ^ a) =
      fun c => ∫ t in (-1 : ℝ)..c, (t ^ a - uniformMean (fun t : ℝ => t ^ a)) :=
    funext (centredPrimitive_X_pow a)
  rw [h]
  exact intervalIntegral.continuous_primitive (fun _ _ =>
    (by fun_prop : Continuous fun t : ℝ => t ^ a - uniformMean (fun t : ℝ => t ^ a)).intervalIntegrable
      _ _) (-1)

/- English proof (translation)
Use `IntervalIntegrable.mono_fun' (g := fun _ => (4 : ℝ)) intervalIntegrable_const ?_ ?_` and prove the remaining obligations. Conclude with `(((continuous_centredPrimitive a).mul (continuous_centredPrimitive b)).measurable.div (by fun_prop)).aestronglyMeasurable`. Use `(ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall fun c hc => ?_)` and prove the remaining obligations. Rewrite `hc` using `[Set.uIoc_of_le (by norm_num)]`. Establish `hc' : c ∈ Set.Icc (-1 : ℝ) 1` using `⟨hc.1.le, hc.2⟩`.

Simplify using `only`. Break down `eq_or_lt_of_le (show (0 : ℝ) ≤ 1 - c ^ 2 by nlinarith [hc'.1, hc'.2]) with h | h` into its components or cases. Simplify using `[← h]`. Rewrite using `[Real.norm_eq_abs, abs_div, abs_of_pos h, div_le_iff₀ h, abs_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem intervalIntegrable_ratio (a b : ℕ) :
    IntervalIntegrable (fun c : ℝ => centredPrimitive (Polynomial.X ^ a) c *
      centredPrimitive (Polynomial.X ^ b) c / (1 - c ^ 2)) volume (-1) 1 := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => (4 : ℝ)) intervalIntegrable_const ?_ ?_
  · exact (((continuous_centredPrimitive a).mul (continuous_centredPrimitive b)).measurable.div
      (by fun_prop)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall fun c hc => ?_)
    rw [Set.uIoc_of_le (by norm_num)] at hc
    have hc' : c ∈ Set.Icc (-1 : ℝ) 1 := ⟨hc.1.le, hc.2⟩
    dsimp only
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ 1 - c ^ 2 by nlinarith [hc'.1, hc'.2]) with h | h
    · simp [← h]
    · rw [Real.norm_eq_abs, abs_div, abs_of_pos h, div_le_iff₀ h, abs_mul]
      calc |centredPrimitive (Polynomial.X ^ a) c| * |centredPrimitive (Polynomial.X ^ b) c|
          ≤ (2 * (c + 1)) * (2 * (1 - c)) :=
            mul_le_mul (abs_centredPrimitive_le_left a hc') (abs_centredPrimitive_le_right b hc')
              (abs_nonneg _) (by linarith [hc'.1])
        _ = 4 * (1 - c ^ 2) := by ring

/- English proof (translation)
Rewrite using `[integral_expand h0, squareMean_eq]`. Repeatedly rewrite using `[term_eq h0, doublyCentred_eq, Finset.sum_div]`. Rewrite using `[intervalIntegral.integral_finsetSum (fun d _ => by`. Use `(intervalIntegrable_ratio (d 0) (d 1)).const_mul (g.coeff d) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `c`.

Use the proof step `ring)]`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Repeatedly rewrite using `[mul_div_assoc]`. Rewrite using `[intervalIntegral.integral_const_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem bilinear_extended (h0 : ZonalBilinearFormula.Statement) (g : MvPolynomial (Fin 2) ℝ) :
    ∫ p, kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * eval ![height p.1, height p.2] g ∂pairMeasure =
      -(1 / 2) * squareMean g - (1 / 4) * ∫ c in (-1 : ℝ)..1, doublyCentred g c / (1 - c ^ 2) := by
  rw [integral_expand h0, squareMean_eq]
  simp_rw [term_eq h0, doublyCentred_eq, Finset.sum_div]
  rw [intervalIntegral.integral_finsetSum (fun d _ => by
    convert (intervalIntegrable_ratio (d 0) (d 1)).const_mul (g.coeff d) using 1
    funext c
    ring)]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp_rw [mul_div_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

/- English proof (translation)
Establish `hgeom : (1 - c ^ 2) * ∑ j ∈ Finset.range k, (c ^ 2) ^ j = 1 - (c ^ 2) ^ k` using `mul_neg_geom_sum (c ^ 2) k`. Rewrite `hgeom` using `[← pow_mul]`. Break down `eq_or_ne (1 - c ^ 2) 0 with h | h` into its components or cases. Establish `hc2 : c ^ 2 = 1` using `by linarith`. Establish `hpow : ∀ j : ℕ, c ^ (2 * j) = 1` using `fun j => by rw [pow_mul, hc2, one_pow]`.

Simplify using `[h, hpow]`. Rewrite using `[div_eq_iff h, ← hgeom]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gHat_div (k : ℕ) (c : ℝ) :
    ((1 - c ^ (2 * k)) - k * (1 - c ^ 2)) / (1 - c ^ 2) =
      ∑ j ∈ Finset.range k, c ^ (2 * j) - k := by
  have hgeom : (1 - c ^ 2) * ∑ j ∈ Finset.range k, (c ^ 2) ^ j = 1 - (c ^ 2) ^ k :=
    mul_neg_geom_sum (c ^ 2) k
  simp_rw [← pow_mul] at hgeom
  rcases eq_or_ne (1 - c ^ 2) 0 with h | h
  · have hc2 : c ^ 2 = 1 := by linarith
    have hpow : ∀ j : ℕ, c ^ (2 * j) = 1 := fun j => by rw [pow_mul, hc2, one_pow]
    simp [h, hpow]
  · rw [div_eq_iff h, ← hgeom]
    ring

/- English proof (translation)
Rewrite using `[integral_pow]`. Establish `h : (-1 : ℝ) ^ (2 * j + 1) = -1` using `by rw [pow_succ, pow_mul]; norm_num`. Rewrite using `[h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_even_pow (j : ℕ) : ∫ c in (-1 : ℝ)..1, c ^ (2 * j) = 2 / (2 * j + 1) := by
  rw [integral_pow]
  have h : (-1 : ℝ) ^ (2 * j + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [h]
  push_cast
  ring

end FibreConstantClosedForm

open FibreConstantClosedForm in

/- English proof (translation)
Establish `key : ∀ k : ℕ, fibreConstant k = -(1 / 2) * ∑ j ∈ Finset.range k, (1 : ℝ) / (2 * j + 1)`. Introduce `k`. Rewrite using `[fibreConstant, bilinear_extended h0, (h1 k).1]`. Repeatedly rewrite using `[(h1 k).2, gHat_div]`. Rewrite using `[intervalIntegral.integral_sub ((by fun_prop : Continuous fun c : ℝ => ∑ j ∈ Finset.range k, c ^ (2 * j)).intervalIntegrable _ _) intervalIntegrable_const, isum _ _ _ _ (fun j _ => by fun_prop), intervalIntegral.integral_const]`.

Repeatedly rewrite using `[integral_even_pow]`. Establish `: ∑ j ∈ Finset.range k, (2 : ℝ) / (2 * j + 1) = 2 * ∑ j ∈ Finset.range k, (1 : ℝ) / (2 * j + 1)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `refine ⟨key, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [key] <;> norm_num [Finset.sum_range_succ]`.
-/
theorem FibreConstantClosedForm.proof (h0 : ZonalBilinearFormula.Statement)
    (h1 : GHatIdentity.Statement) : FibreConstantClosedForm.Statement := by
  have key : ∀ k : ℕ, fibreConstant k = -(1 / 2) * ∑ j ∈ Finset.range k, (1 : ℝ) / (2 * j + 1) := by
    intro k
    rw [fibreConstant, bilinear_extended h0, (h1 k).1]
    simp_rw [(h1 k).2, gHat_div]
    rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun c : ℝ =>
        ∑ j ∈ Finset.range k, c ^ (2 * j)).intervalIntegrable _ _) intervalIntegrable_const,
      isum _ _ _ _ (fun j _ => by fun_prop), intervalIntegral.integral_const]
    simp_rw [integral_even_pow]
    have : ∑ j ∈ Finset.range k, (2 : ℝ) / (2 * j + 1) =
        2 * ∑ j ∈ Finset.range k, (1 : ℝ) / (2 * j + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, smul_eq_mul]
    ring
  refine ⟨key, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [key] <;> norm_num [Finset.sum_range_succ]
