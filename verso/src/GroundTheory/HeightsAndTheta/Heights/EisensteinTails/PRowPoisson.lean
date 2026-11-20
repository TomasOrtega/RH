import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EisensteinTails.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LeavesOrthogonalSum

open Complex MeasureTheory Filter Asymptotics
open scoped Real FourierTransform

noncomputable section

namespace RowPoisson

def pw (Y : ℝ) (a : ℂ) (t : ℝ) : ℂ :=
  ((t ^ 2 + Y ^ 2 : ℝ) : ℂ) ^ (-a)

/- English proof (translation)
Check the signs of the components of the expression.
-/
theorem base_pos {Y : ℝ} (hY : 0 < Y) (t : ℝ) : 0 < t ^ 2 + Y ^ 2 := by positivity

/- English proof (translation)
Rewrite using `[pw, norm_cpow_eq_rpow_re_of_pos (base_pos hY t), neg_re]`.
-/
theorem norm_pw {Y : ℝ} (hY : 0 < Y) (a : ℂ) (t : ℝ) :
    ‖pw Y a t‖ = (t ^ 2 + Y ^ 2) ^ (-a.re) := by
  rw [pw, norm_cpow_eq_rpow_re_of_pos (base_pos hY t), neg_re]

/- English proof (translation)
Establish `h1 : Integrable (fun u : ℝ ↦ ((1 : ℝ) + ‖u‖ ^ 2) ^ (-(2 * r) / 2))` using `integrable_rpow_neg_one_add_norm_sq (by simp; linarith)`. Establish `h2` using `(h1.comp_div hY.ne').const_mul ((Y ^ 2) ^ (-r))`. Use `h2.congr (ae_of_all _ fun t ↦ ?_)` and prove the remaining obligations. Use `show (Y ^ 2) ^ (-r) * (1 + ‖t / Y‖ ^ 2) ^ (-(2 * r) / 2) = (t ^ 2 + Y ^ 2) ^ (-r)`. Rewrite using `[show -(2 * r) / 2 = -r by ring, Real.norm_eq_abs, sq_abs, ← Real.mul_rpow (by positivity) (by positivity)]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integrable_rpow {Y r : ℝ} (hY : 0 < Y) (hr : 1 / 2 < r) :
    Integrable (fun t : ℝ ↦ (t ^ 2 + Y ^ 2) ^ (-r)) := by
  have h1 : Integrable (fun u : ℝ ↦ ((1 : ℝ) + ‖u‖ ^ 2) ^ (-(2 * r) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by simp; linarith)
  have h2 := (h1.comp_div hY.ne').const_mul ((Y ^ 2) ^ (-r))
  refine h2.congr (ae_of_all _ fun t ↦ ?_)
  show (Y ^ 2) ^ (-r) * (1 + ‖t / Y‖ ^ 2) ^ (-(2 * r) / 2) = (t ^ 2 + Y ^ 2) ^ (-r)
  rw [show -(2 * r) / 2 = -r by ring, Real.norm_eq_abs, sq_abs,
    ← Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

/- English proof (translation)
Rewrite using `[neg_add, Real.rpow_add hB, Real.rpow_neg hB.le c]`. Establish `hc : 0 < B ^ c` using `Real.rpow_pos_of_pos hB c`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_rpow_le {B x r c : ℝ} (hB : 0 < B) (hxB : x ≤ B ^ c) :
    x * B ^ (-(r + c)) ≤ B ^ (-r) := by
  rw [neg_add, Real.rpow_add hB, Real.rpow_neg hB.le c]
  have hc : 0 < B ^ c := Real.rpow_pos_of_pos hB c
  calc x * (B ^ (-r) * (B ^ c)⁻¹) = B ^ (-r) * (x / B ^ c) := by ring
    _ ≤ B ^ (-r) * 1 := by gcongr; exact (div_le_one hc).2 hxB
    _ = B ^ (-r) := mul_one _

/- English proof (translation)
Establish `hq : HasDerivAt (fun u : ℝ ↦ u ^ 2 + Y ^ 2) (2 * t) t`. Simplify using `using (hasDerivAt_pow 2 t).add_const (Y ^ 2)`. Establish `h0 : ((t ^ 2 + Y ^ 2 : ℝ) : ℂ) ∈ slitPlane` using `ofReal_mem_slitPlane.2 (base_pos hY t)`. Use `(Complex.hasStrictDerivAt_cpow_const (c := -a) h0).hasDerivAt.comp t hq.ofReal_comp` as an intermediate fact. Establish `e1 : pw Y a = (fun z : ℂ ↦ z ^ (-a)) ∘ fun y : ℝ ↦ ((y ^ 2 + Y ^ 2 : ℝ) : ℂ)` using `rfl`.

Establish `e2 : -a * pw Y (a + 1) t * ((2 * t : ℝ) : ℂ) = -a * ((t ^ 2 + Y ^ 2 : ℝ) : ℂ) ^ (-a - 1) * ((2 * t : ℝ) : ℂ)`. Rewrite using `[pw, neg_add']`. Rewrite using `[e1, e2]`. Conclude with `this`. Use the proof step `@[fun_prop]`.
-/
theorem hasDerivAt_pw {Y : ℝ} (hY : 0 < Y) (a : ℂ) (t : ℝ) :
    HasDerivAt (pw Y a) (-a * pw Y (a + 1) t * ((2 * t : ℝ) : ℂ)) t := by
  have hq : HasDerivAt (fun u : ℝ ↦ u ^ 2 + Y ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const (Y ^ 2)
  have h0 : ((t ^ 2 + Y ^ 2 : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 (base_pos hY t)
  have := (Complex.hasStrictDerivAt_cpow_const (c := -a) h0).hasDerivAt.comp t hq.ofReal_comp
  have e1 : pw Y a = (fun z : ℂ ↦ z ^ (-a)) ∘ fun y : ℝ ↦ ((y ^ 2 + Y ^ 2 : ℝ) : ℂ) := rfl
  have e2 : -a * pw Y (a + 1) t * ((2 * t : ℝ) : ℂ) =
      -a * ((t ^ 2 + Y ^ 2 : ℝ) : ℂ) ^ (-a - 1) * ((2 * t : ℝ) : ℂ) := by
    rw [pw, neg_add']
  rw [e1, e2]
  exact this

@[fun_prop]
/- English proof (translation)
The claim follows from `continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_pw hY a t).continuousAt`.
-/
theorem continuous_pw {Y : ℝ} (hY : 0 < Y) (a : ℂ) : Continuous (pw Y a) :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_pw hY a t).continuousAt

/- English proof (translation)
Rewrite using `[Real.fourier_real_eq]`. Use `(norm_integral_le_integral_norm _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `v`. Conclude with `Circle.norm_smul _ _`.
-/
theorem norm_fourier_le {f : ℝ → ℂ} (w : ℝ) : ‖𝓕 f w‖ ≤ ∫ v, ‖f v‖ := by
  rw [Real.fourier_real_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext v
  exact Circle.norm_smul _ _

end RowPoisson

open RowPoisson in

/- English proof (translation)
Introduce `τ m hm s hs`. Use `set σ := s.re with hσ`. Use `set x : ℝ := (m : ℝ) * τ.re with hx`. Use `set Y : ℝ := |(m : ℝ)| * τ.im with hYdef`. Establish `hY : 0 < Y` using `mul_pos (abs_pos.2 (Int.cast_ne_zero.2 hm)) τ.im_pos`.

Use `set f0 : ℝ → ℂ := pw Y s with hf0`. Use `set f1 : ℝ → ℂ := fun t ↦ -s * pw Y (s + 1) t * ((2 * t : ℝ) : ℂ) with hf1`. Use `set f2 : ℝ → ℂ := fun t ↦ -s * (-(s + 1) * pw Y (s + 1 + 1) t * ((2 * t : ℝ) : ℂ)) * ((2 * t : ℝ) : ℂ) + -s * pw Y (s + 1) t * ((2 : ℝ) : ℂ) with hf2`. Establish `d0 : ∀ t, HasDerivAt f0 (f1 t) t` using `fun t ↦ hasDerivAt_pw hY s t`. Establish `d1 : ∀ t, HasDerivAt f1 (f2 t) t`.

Introduce `t`. Establish `hl : HasDerivAt (fun u : ℝ ↦ ((2 * u : ℝ) : ℂ)) ((2 : ℝ) : ℂ) t`. Simplify using `using ((hasDerivAt_id t).const_mul (2 : ℝ)).ofReal_comp`. Conclude with `((hasDerivAt_pw hY (s + 1) t).const_mul (-s)).mul hl`. Establish `deriv0 : deriv f0 = f1` using `funext fun t ↦ (d0 t).deriv`.

Establish `deriv1 : deriv f1 = f2` using `funext fun t ↦ (d1 t).deriv`. Establish `diff0 : Differentiable ℝ f0` using `fun t ↦ (d0 t).differentiableAt`. Establish `diff1 : Differentiable ℝ f1` using `fun t ↦ (d1 t).differentiableAt`. Establish `c2 : Continuous f2`. Simplify using `only [hf2]`.

Use `fun_prop (disch := exact hY)`. Establish `int0 : Integrable f0`. Use `(integrable_rpow hY (r := σ) hs).mono' diff0.continuous.aestronglyMeasurable (ae_of_all _ fun t ↦ ?_)` and prove the remaining obligations. Rewrite using `[hf0, norm_pw hY]`. Establish `int1 : Integrable f1`.

Use `((integrable_rpow hY (r := σ + 1 / 2) (by linarith)).const_mul (2 * ‖s‖)).mono' diff1.continuous.aestronglyMeasurable (ae_of_all _ fun t ↦ ?_)` and prove the remaining obligations. Establish `hB` using `base_pos hY t`. Establish `ht : |t| ≤ (t ^ 2 + Y ^ 2) ^ (1 / 2 : ℝ)`. Rewrite using `[← Real.sqrt_eq_rpow]; exact Real.abs_le_sqrt (by nlinarith)`. Establish `key` using `mul_rpow_le (r := σ + 1 / 2) hB ht`.

Establish `hre : (s + 1).re = σ + 1 / 2 + 1 / 2` using `by simp [hσ]; ring`. Simplify using `only [hf1, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_pw hY, hre, abs_two]`. Combine the equalities or inequalities in the displayed calculation. Establish `int2 : Integrable f2`. Use `((integrable_rpow hY (r := σ + 1) (by linarith)).const_mul (‖s‖ * (4 * ‖s + 1‖ + 2))).mono' c2.aestronglyMeasurable (ae_of_all _ fun t ↦ ?_)` and prove the remaining obligations.

Establish `hB` using `base_pos hY t`. Establish `ht : t ^ 2 ≤ (t ^ 2 + Y ^ 2) ^ (1 : ℝ)` using `by rw [Real.rpow_one]; nlinarith`. Establish `key` using `mul_rpow_le (r := σ + 1) hB ht`. Establish `hre1 : (s + 1).re = σ + 1` using `by simp [hσ]`. Establish `hre2 : (s + 1 + 1).re = σ + 1 + 1` using `by simp [hσ]`.

Establish `hpos : 0 ≤ (t ^ 2 + Y ^ 2) ^ (-(σ + 1))` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_pw hY, hre1, hre2, abs_two]`. Rewrite using `[← sq_abs t]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ ‖s‖ * ‖s + 1‖ * 4 * (t ^ 2 + Y ^ 2) ^ (-(σ + 1)) + 2 * ‖s‖ * (t ^ 2 + Y ^ 2) ^ (-(σ + 1)) := by`. Rewrite using `[show σ + 1 + 1 = (σ + 1) + 1 by ring]; gcongr`. Use `_ = ‖s‖ * (4 * ‖s + 1‖ + 2) * (t ^ 2 + Y ^ 2) ^ (-(σ + 1)) := by ring`. Establish `F1` using `Real.fourier_deriv int0 diff0 (deriv0 ▸ int1)`. Establish `F2` using `Real.fourier_deriv int1 diff1 (deriv1 ▸ int2)`.

Rewrite `F1` using `[deriv0]`. Rewrite `F2` using `[deriv1]`. Use `set M : ℝ := ∫ v, ‖f2 v‖`. Establish `bound : ∀ w : ℝ, w ≠ 0 → ‖𝓕 f0 w‖ ≤ M / (2 * π) ^ 2 * |w| ^ (-2 : ℝ)`. Introduce `w hw`.

Establish `e : 𝓕 f2 w = (2 * π * I * w) • (2 * π * I * w) • 𝓕 f0 w`. Rewrite using `[F2, F1]`. Establish `hn : ‖𝓕 f2 w‖ = (2 * π * |w|) ^ 2 * ‖𝓕 f0 w‖`. Rewrite using `[e, norm_smul, norm_smul]`. Establish `: ‖(2 * π * I * w : ℂ)‖ = 2 * π * |w|`.

Simplify using `[Complex.norm_real, abs_of_pos Real.pi_pos]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hle` using `norm_fourier_le (f := f2) w`. Establish `hw' : 0 < |w|` using `abs_pos.2 hw`.

Rewrite using `[Real.rpow_neg (abs_nonneg w), Real.rpow_two, ← div_eq_mul_inv, div_div, le_div_iff₀ (by positivity)]`. Use polynomial arithmetic with `[hn, hle]`. Establish `sumF : Summable fun n : ℤ ↦ 𝓕 f0 n`. Use `Summable.of_norm_bounded_eventually ((Real.summable_abs_int_rpow one_lt_two).mul_left (M / (2 * π) ^ 2)) ?_` and prove the remaining obligations. Use `filter_upwards [eventually_cofinite_ne 0] with n hn`.

Conclude with `bound n (Int.cast_ne_zero.2 hn)`. Establish `decay : f0 =O[cocompact ℝ] fun t : ℝ ↦ |t| ^ (-(2 * σ))`. Use `IsBigO.of_bound 1 ?_` and prove the remaining obligations. Use `filter_upwards [(isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact] with t ht`. Establish `ht0 : t ≠ 0` using `ht`.

Establish `hpos : 0 < t ^ 2` using `by positivity`. Rewrite using `[one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _), hf0, norm_pw hY, Real.rpow_neg (by positivity), Real.rpow_neg (abs_nonneg t), Real.rpow_mul (abs_nonneg t), Real.rpow_two, sq_abs]`. Conclude with `inv_anti₀ (Real.rpow_pos_of_pos hpos σ) (Real.rpow_le_rpow hpos.le (by nlinarith [sq_nonneg Y]) (by linarith))`. Establish `P` using `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable diff0.continuous (b := 2 * σ) (by linarith) decay sumF x`. Establish `lhs : rowSum m τ s = ∑' n : ℤ, f0 (x + n)`.

Unfold `rowSum`. Use `congr 1`. Use function extensionality and compare the values at `n`. Establish `hsq : ‖(m : ℂ) * (τ : ℂ) + n‖ ^ 2 = (x + n) ^ 2 + Y ^ 2`. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`.

Simplify using `[hx, hYdef, mul_pow, sq_abs]`. Expand and normalize the polynomial expressions, which then agree. Establish `hr : 0 < ‖(m : ℂ) * (τ : ℂ) + n‖`. Use `base_pos hY (x + n)` as an intermediate fact. Rewrite `this` using `[← hsq]`.

Break down `(norm_nonneg ((m : ℂ) * (τ : ℂ) + n)).lt_or_eq with h | h` into its components or cases. Conclude with `h`. Rewrite `this` using `[← h]`. Simplify using `at this`. Rewrite using `[hf0, pw, ← hsq]`.

Use `set r := ‖(m : ℂ) * (τ : ℂ) + n‖`. Establish `hr0 : ((r : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hr.ne'`. Establish `hr20 : ((r ^ 2 : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (pow_pos hr 2).ne'`. Rewrite using `[cpow_def_of_ne_zero hr0, cpow_def_of_ne_zero hr20, ← ofReal_log hr.le, ← ofReal_log (pow_pos hr 2).le, Real.log_pow]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[lhs, P]`. Use `congr 1`. Use function extensionality and compare the values at `n`.

Rewrite using `[fourier_coe_apply, mul_comm]`. Use `congr 1`. Unfold `expTwoPiI`. Use `congr 1`. Simplify using `[hx]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Real.fourier_real_eq]`. Unfold `freqIntegral`. Use `congr 1`. Use function extensionality and compare the values at `t`.

Rewrite using `[Circle.smul_def, Real.fourierChar_apply, hf0, pw, smul_eq_mul]`. Unfold `expTwoPiI`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem RowPoisson.proof : RowPoisson.Statement := by
  intro τ m hm s hs
  set σ := s.re with hσ
  set x : ℝ := (m : ℝ) * τ.re with hx
  set Y : ℝ := |(m : ℝ)| * τ.im with hYdef
  have hY : 0 < Y := mul_pos (abs_pos.2 (Int.cast_ne_zero.2 hm)) τ.im_pos

  set f0 : ℝ → ℂ := pw Y s with hf0
  set f1 : ℝ → ℂ := fun t ↦ -s * pw Y (s + 1) t * ((2 * t : ℝ) : ℂ) with hf1
  set f2 : ℝ → ℂ := fun t ↦ -s * (-(s + 1) * pw Y (s + 1 + 1) t * ((2 * t : ℝ) : ℂ)) *
    ((2 * t : ℝ) : ℂ) + -s * pw Y (s + 1) t * ((2 : ℝ) : ℂ) with hf2
  have d0 : ∀ t, HasDerivAt f0 (f1 t) t := fun t ↦ hasDerivAt_pw hY s t
  have d1 : ∀ t, HasDerivAt f1 (f2 t) t := by
    intro t
    have hl : HasDerivAt (fun u : ℝ ↦ ((2 * u : ℝ) : ℂ)) ((2 : ℝ) : ℂ) t := by
      simpa using ((hasDerivAt_id t).const_mul (2 : ℝ)).ofReal_comp
    exact ((hasDerivAt_pw hY (s + 1) t).const_mul (-s)).mul hl
  have deriv0 : deriv f0 = f1 := funext fun t ↦ (d0 t).deriv
  have deriv1 : deriv f1 = f2 := funext fun t ↦ (d1 t).deriv
  have diff0 : Differentiable ℝ f0 := fun t ↦ (d0 t).differentiableAt
  have diff1 : Differentiable ℝ f1 := fun t ↦ (d1 t).differentiableAt
  have c2 : Continuous f2 := by
    simp only [hf2]
    fun_prop (disch := exact hY)

  have int0 : Integrable f0 := by
    refine (integrable_rpow hY (r := σ) hs).mono' diff0.continuous.aestronglyMeasurable
      (ae_of_all _ fun t ↦ ?_)
    rw [hf0, norm_pw hY]
  have int1 : Integrable f1 := by
    refine ((integrable_rpow hY (r := σ + 1 / 2) (by linarith)).const_mul (2 * ‖s‖)).mono'
      diff1.continuous.aestronglyMeasurable (ae_of_all _ fun t ↦ ?_)
    have hB := base_pos hY t
    have ht : |t| ≤ (t ^ 2 + Y ^ 2) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.abs_le_sqrt (by nlinarith)
    have key := mul_rpow_le (r := σ + 1 / 2) hB ht
    have hre : (s + 1).re = σ + 1 / 2 + 1 / 2 := by simp [hσ]; ring
    simp only [hf1, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_pw hY, hre, abs_two]
    calc ‖s‖ * (t ^ 2 + Y ^ 2) ^ (-(σ + 1 / 2 + 1 / 2)) * (2 * |t|)
        = 2 * ‖s‖ * (|t| * (t ^ 2 + Y ^ 2) ^ (-(σ + 1 / 2 + 1 / 2))) := by ring
      _ ≤ 2 * ‖s‖ * (t ^ 2 + Y ^ 2) ^ (-(σ + 1 / 2)) := by gcongr
  have int2 : Integrable f2 := by
    refine ((integrable_rpow hY (r := σ + 1) (by linarith)).const_mul
      (‖s‖ * (4 * ‖s + 1‖ + 2))).mono' c2.aestronglyMeasurable (ae_of_all _ fun t ↦ ?_)
    have hB := base_pos hY t
    have ht : t ^ 2 ≤ (t ^ 2 + Y ^ 2) ^ (1 : ℝ) := by rw [Real.rpow_one]; nlinarith
    have key := mul_rpow_le (r := σ + 1) hB ht
    have hre1 : (s + 1).re = σ + 1 := by simp [hσ]
    have hre2 : (s + 1 + 1).re = σ + 1 + 1 := by simp [hσ]
    have hpos : 0 ≤ (t ^ 2 + Y ^ 2) ^ (-(σ + 1)) := by positivity
    calc ‖f2 t‖ ≤ ‖-s * (-(s + 1) * pw Y (s + 1 + 1) t * ((2 * t : ℝ) : ℂ)) *
          ((2 * t : ℝ) : ℂ)‖ + ‖-s * pw Y (s + 1) t * ((2 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = ‖s‖ * ‖s + 1‖ * 4 * (t ^ 2 * (t ^ 2 + Y ^ 2) ^ (-(σ + 1 + 1))) +
          2 * ‖s‖ * (t ^ 2 + Y ^ 2) ^ (-(σ + 1)) := by
        simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_pw hY, hre1,
          hre2, abs_two]
        rw [← sq_abs t]
        ring
      _ ≤ ‖s‖ * ‖s + 1‖ * 4 * (t ^ 2 + Y ^ 2) ^ (-(σ + 1)) +
          2 * ‖s‖ * (t ^ 2 + Y ^ 2) ^ (-(σ + 1)) := by
        rw [show σ + 1 + 1 = (σ + 1) + 1 by ring]; gcongr
      _ = ‖s‖ * (4 * ‖s + 1‖ + 2) * (t ^ 2 + Y ^ 2) ^ (-(σ + 1)) := by ring

  have F1 := Real.fourier_deriv int0 diff0 (deriv0 ▸ int1)
  have F2 := Real.fourier_deriv int1 diff1 (deriv1 ▸ int2)
  rw [deriv0] at F1
  rw [deriv1] at F2
  set M : ℝ := ∫ v, ‖f2 v‖
  have bound : ∀ w : ℝ, w ≠ 0 → ‖𝓕 f0 w‖ ≤ M / (2 * π) ^ 2 * |w| ^ (-2 : ℝ) := by
    intro w hw
    have e : 𝓕 f2 w = (2 * π * I * w) • (2 * π * I * w) • 𝓕 f0 w := by
      rw [F2, F1]
    have hn : ‖𝓕 f2 w‖ = (2 * π * |w|) ^ 2 * ‖𝓕 f0 w‖ := by
      rw [e, norm_smul, norm_smul]
      have : ‖(2 * π * I * w : ℂ)‖ = 2 * π * |w| := by
        simp [Complex.norm_real, abs_of_pos Real.pi_pos]
      rw [this]; ring
    have hle := norm_fourier_le (f := f2) w
    have hw' : 0 < |w| := abs_pos.2 hw
    rw [Real.rpow_neg (abs_nonneg w), Real.rpow_two, ← div_eq_mul_inv, div_div,
      le_div_iff₀ (by positivity)]
    nlinarith [hn, hle]
  have sumF : Summable fun n : ℤ ↦ 𝓕 f0 n := by
    refine Summable.of_norm_bounded_eventually
      ((Real.summable_abs_int_rpow one_lt_two).mul_left (M / (2 * π) ^ 2)) ?_
    filter_upwards [eventually_cofinite_ne 0] with n hn
    exact bound n (Int.cast_ne_zero.2 hn)

  have decay : f0 =O[cocompact ℝ] fun t : ℝ ↦ |t| ^ (-(2 * σ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [(isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact] with t ht
    have ht0 : t ≠ 0 := ht
    have hpos : 0 < t ^ 2 := by positivity
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _), hf0, norm_pw hY,
      Real.rpow_neg (by positivity), Real.rpow_neg (abs_nonneg t), Real.rpow_mul (abs_nonneg t),
      Real.rpow_two, sq_abs]
    exact inv_anti₀ (Real.rpow_pos_of_pos hpos σ)
      (Real.rpow_le_rpow hpos.le (by nlinarith [sq_nonneg Y]) (by linarith))
  have P := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable diff0.continuous
    (b := 2 * σ) (by linarith) decay sumF x

  have lhs : rowSum m τ s = ∑' n : ℤ, f0 (x + n) := by
    unfold rowSum
    congr 1
    funext n
    have hsq : ‖(m : ℂ) * (τ : ℂ) + n‖ ^ 2 = (x + n) ^ 2 + Y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [hx, hYdef, mul_pow, sq_abs]
      ring
    have hr : 0 < ‖(m : ℂ) * (τ : ℂ) + n‖ := by
      have := base_pos hY (x + n)
      rw [← hsq] at this
      rcases (norm_nonneg ((m : ℂ) * (τ : ℂ) + n)).lt_or_eq with h | h
      · exact h
      · rw [← h] at this; simp at this
    rw [hf0, pw, ← hsq]
    set r := ‖(m : ℂ) * (τ : ℂ) + n‖
    have hr0 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hr20 : ((r ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hr 2).ne'
    rw [cpow_def_of_ne_zero hr0, cpow_def_of_ne_zero hr20, ← ofReal_log hr.le,
      ← ofReal_log (pow_pos hr 2).le, Real.log_pow]
    congr 1
    push_cast
    ring
  rw [lhs, P]
  congr 1
  funext n
  rw [fourier_coe_apply, mul_comm]
  congr 1
  · unfold expTwoPiI
    congr 1
    simp [hx]
    ring
  · rw [Real.fourier_real_eq]
    unfold freqIntegral
    congr 1
    funext t
    rw [Circle.smul_def, Real.fourierChar_apply, hf0, pw, smul_eq_mul]
    unfold expTwoPiI
    congr 2
    push_cast
    ring

end

end GroundTheory.Heights₂.Heights.LeavesOrthogonalSum
