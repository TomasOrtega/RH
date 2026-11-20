import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

/- English proof (translation)
Establish `hr : ‖r‖ < 1`. Rewrite using `[Real.norm_eq_abs, abs_of_pos hr0]`. Conclude with `hr1`. Establish `h` using `(summable_nat_add_iff 1).mpr (summable_pow_mul_geometric_of_norm_lt_one A hr : Summable fun m : ℕ => (m : ℝ) ^ A * r ^ m)`. Use `(h.mul_left (C * r⁻¹)).congr fun n => ?_` and prove the remaining obligations.

Establish `hr' : r ≠ 0` using `hr0.ne'`. Use `push_cast`. Rewrite using `[pow_succ]`. Clear the denominators using the available nonvanishing facts.
-/
private lemma summable_poly_mul_geometric (C : ℝ) (A : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable fun n : ℕ => C * ((n : ℝ) + 1) ^ A * r ^ n := by
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have h := (summable_nat_add_iff 1).mpr
    (summable_pow_mul_geometric_of_norm_lt_one A hr : Summable fun m : ℕ => (m : ℝ) ^ A * r ^ m)
  refine (h.mul_left (C * r⁻¹)).congr fun n => ?_
  have hr' : r ≠ 0 := hr0.ne'
  push_cast
  rw [pow_succ]
  field_simp

/- English proof (translation)
Rewrite using `[norm_mul, Complex.norm_exp]`. Establish `hre : (2 * π * Complex.I * n * w).re = -(2 * π * n * w.im)`. Simplify using `[Complex.mul_re, Complex.mul_im]`. Rewrite using `[hre]`. Establish `hexp : Real.exp (-(2 * π * n * w.im)) ≤ Real.exp (-(2 * π * y0)) ^ n`.

Rewrite using `[← Real.exp_nat_mul]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Establish `hp : (0:ℝ) ≤ 2 * π * n` using `by positivity`. Use `mul_le_mul_of_nonneg_left hw.le hp` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `mul_le_mul (hC n) hexp (Real.exp_pos _).le (le_trans (norm_nonneg _) (hC n))`.
-/
private lemma qs_term_bound (a : ℕ → ℂ) (C : ℝ) (A : ℕ) (hC : ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ A)
    (y0 : ℝ) (n : ℕ) (w : ℂ) (hw : y0 < w.im) :
    ‖a n * cexp (2 * π * Complex.I * n * w)‖ ≤ C * ((n : ℝ) + 1) ^ A * Real.exp (-(2 * π * y0)) ^ n := by
  rw [norm_mul, Complex.norm_exp]
  have hre : (2 * π * Complex.I * n * w).re = -(2 * π * n * w.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  have hexp : Real.exp (-(2 * π * n * w.im)) ≤ Real.exp (-(2 * π * y0)) ^ n := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hp : (0:ℝ) ≤ 2 * π * n := by positivity
    have := mul_le_mul_of_nonneg_left hw.le hp
    nlinarith
  exact mul_le_mul (hC n) hexp (Real.exp_pos _).le (le_trans (norm_nonneg _) (hC n))

/- English proof (translation)
Introduce and unpack `a ⟨C, A, hC⟩`. Rewrite using `[UpperHalfPlane.mdifferentiable_iff]`. Introduce `z hz`. Establish `hz' : 0 < z.im` using `hz`. Use `set y0 := z.im / 2 with hy0def`.

Establish `hy0 : 0 < y0` using `by positivity`. Use `set U : Set ℂ := {w | y0 < w.im} with hUdef`. Establish `hU : IsOpen U` using `isOpen_lt continuous_const Complex.continuous_im`. Establish `hzU : z ∈ U` using `by show y0 < z.im`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hr0 : 0 < Real.exp (-(2 * π * y0))` using `Real.exp_pos _`. Establish `hr1 : Real.exp (-(2 * π * y0)) < 1`. Rewrite using `[Real.exp_lt_one_iff]`. Use `Real.pi_pos` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `hD : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * w)) U` using `Complex.differentiableOn_tsum_of_summable_norm (summable_poly_mul_geometric C A hr0 hr1) (fun n => (by fun_prop : Differentiable ℂ fun w : ℂ => a n * cexp (2 * π * Complex.I * n * w)).differentiableOn) hU (fun n w hw => qs_term_bound a C A hC y0 n w hw)`. Establish `hDz` using `(hD z hzU).differentiableAt (hU.mem_nhds hzU)`. Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises. Apply `hDz.congr_of_eventuallyEq` to reduce the goal to its premises. Use `filter_upwards [hU.mem_nhds hzU] with w hw`.

Establish `hw' : 0 < w.im` using `lt_trans hy0 hw`. Rewrite using `[Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw']`. Both sides reduce to the same expression.
-/
theorem qs_mdifferentiable : ∀ a : ℕ → ℂ, PolyB a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qs a) := by
  rintro a ⟨C, A, hC⟩
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have hz' : 0 < z.im := hz
  set y0 := z.im / 2 with hy0def
  have hy0 : 0 < y0 := by positivity
  set U : Set ℂ := {w | y0 < w.im} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hzU : z ∈ U := by
    show y0 < z.im
    linarith
  have hr0 : 0 < Real.exp (-(2 * π * y0)) := Real.exp_pos _
  have hr1 : Real.exp (-(2 * π * y0)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have := Real.pi_pos
    nlinarith
  have hD : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * w)) U :=
    Complex.differentiableOn_tsum_of_summable_norm (summable_poly_mul_geometric C A hr0 hr1)
      (fun n => (by fun_prop : Differentiable ℂ fun w : ℂ => a n * cexp (2 * π * Complex.I * n * w)).differentiableOn)
      hU (fun n w hw => qs_term_bound a C A hC y0 n w hw)
  have hDz := (hD z hzU).differentiableAt (hU.mem_nhds hzU)
  apply DifferentiableAt.differentiableWithinAt
  apply hDz.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hzU] with w hw
  have hw' : 0 < w.im := lt_trans hy0 hw
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw']
  rfl

end GlobalTheory.EisM
