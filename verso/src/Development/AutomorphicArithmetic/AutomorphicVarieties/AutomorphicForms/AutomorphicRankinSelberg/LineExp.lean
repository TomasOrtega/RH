import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open MeasureTheory Set CongruenceSubgroup UpperTheory.V.Af
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ComplexConjugate

namespace UpperTheory.V.Af.Rs

private noncomputable def ex (n : ℕ) (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * n * x)

/- English proof (translation)
Unfold `ex`. Establish `h : (2 * Real.pi * Complex.I * n * x : ℂ) = ((2 * Real.pi * n * x : ℝ) : ℂ) * Complex.I`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, Complex.norm_exp_ofReal_mul_I]`.
-/
private theorem ex_norm (n : ℕ) (x : ℝ) : ‖ex n x‖ = 1 := by
  unfold ex
  have h : (2 * Real.pi * Complex.I * n * x : ℂ) = ((2 * Real.pi * n * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Unfold `ex`. Use `fun_prop`.
-/
private theorem ex_cont (n : ℕ) : Continuous (ex n) := by unfold ex; fun_prop

/- English proof (translation)
Unfold `ex`. Establish `key : ∀ x : ℝ, conj (Complex.exp (2 * Real.pi * Complex.I * m * x)) * Complex.exp (2 * Real.pi * Complex.I * n * x) = Complex.exp ((2 * Real.pi * Complex.I * ((n : ℂ) - m)) * x)`. Introduce `x`. Rewrite using `[← Complex.exp_conj, ← Complex.exp_add]`. Use `congr 1`.

Simplify using `only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[key]`. Use `split_ifs with hmn`. Substitute `hmn` using the available equality.

Simplify using the standard rewrite rules. Establish `hc : (2 * Real.pi * Complex.I * ((n : ℂ) - m)) ≠ 0`. Establish `h1 : ((n : ℂ) - m) ≠ 0`. Rewrite using `[sub_ne_zero]`. Conclude with `(Ne.symm hmn)` after adjusting the coercions.

Establish `h2 : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Simplify using `[h1, h2, Complex.I_ne_zero]`. Rewrite using `[integral_exp_mul_complex hc]`. Establish `e1 : Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) - m) * ((1 : ℝ) : ℂ)) = 1`. Use `Complex.exp_int_mul_two_pi_mul_I ((n : ℤ) - m)` as an intermediate fact.

Rewrite using `[← this]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`.

Simplify using the standard rewrite rules.
-/
private theorem ex_orth (m n : ℕ) : ∫ x in (0 : ℝ)..1, conj (ex m x) * ex n x = if m = n then 1 else 0 := by
  unfold ex
  have key : ∀ x : ℝ, conj (Complex.exp (2 * Real.pi * Complex.I * m * x)) *
      Complex.exp (2 * Real.pi * Complex.I * n * x) =
      Complex.exp ((2 * Real.pi * Complex.I * ((n : ℂ) - m)) * x) := by
    intro x
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
    ring
  simp_rw [key]
  split_ifs with hmn
  · subst hmn
    simp
  · have hc : (2 * Real.pi * Complex.I * ((n : ℂ) - m)) ≠ 0 := by
      have h1 : ((n : ℂ) - m) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast (Ne.symm hmn)
      have h2 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [h1, h2, Complex.I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have e1 : Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) - m) * ((1 : ℝ) : ℂ)) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I ((n : ℤ) - m)
      rw [← this]
      congr 1
      push_cast
      ring
    rw [e1]
    simp

/- English proof (translation)
Establish `han : Summable (fun n => ‖a n‖)` using `summable_norm_iff.mpr ha`. Establish `hbn : Summable (fun n => ‖b n‖)` using `summable_norm_iff.mpr hb`. Establish `hGc : Continuous G`. Establish `e : G = fun x => ∑' n, b n * ex n x` using `funext fun x => (hG x).tsum_eq.symm`. Rewrite using `[e]`.

Use `continuous_tsum (fun n => continuous_const.mul (ex_cont n)) hbn ?_` and prove the remaining obligations. Introduce `n x`. Rewrite using `[norm_mul, ex_norm, mul_one]`. Establish `hGb : ∀ t, ‖G t‖ ≤ ∑' n, ‖b n‖`. Introduce `t`.

Rewrite using `[← (hG t).tsum_eq]`. Establish `e : (fun n => ‖b n * ex n t‖) = fun n => ‖b n‖`. Use function extensionality and compare the values at `n`. Rewrite using `[norm_mul, ex_norm, mul_one]`. Use `(norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[e]`. Conclude with `hbn`. Rewrite using `[e]`. Establish `hC : ∀ n, ∫ x in (0 : ℝ)..1, conj (G x) * ex n x = conj (b n)`. Introduce `n`.

Establish `hs : HasSum (fun m => ∫ x in (0 : ℝ)..1, conj (b m) * (conj (ex m x) * ex n x)) (∫ x in (0 : ℝ)..1, conj (G x) * ex n x)`. Use `intervalIntegral.hasSum_integral_of_dominated_convergence (fun m _ => ‖b m‖) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `m`. Conclude with `(continuous_const.mul ((Complex.continuous_conj.comp (ex_cont m)).mul (ex_cont n))).aestronglyMeasurable`. Introduce `m`.

Use `Filter.Eventually.of_forall (fun t _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, ex_norm, ex_norm]`. Simplify using the standard rewrite rules. Conclude with `Filter.Eventually.of_forall (fun t _ => hbn)`. Conclude with `intervalIntegrable_const`.

Use `Filter.Eventually.of_forall (fun t _ => ?_)` and prove the remaining obligations. Establish `e : (fun m => conj (b m) * (conj (ex m t) * ex n t)) = fun m => conj (b m * ex m t) * ex n t`. Use function extensionality and compare the values at `m`. Rewrite using `[map_mul, mul_assoc]`. Rewrite using `[e]`.

Conclude with `(Complex.hasSum_conj'.mpr (hG t)).mul_right (ex n t)`. Rewrite `hs` using `[intervalIntegral.integral_const_mul, ex_orth]`. Establish `h2 : HasSum (fun m => conj (b m) * if m = n then (1 : ℂ) else 0) (conj (b n))`. Establish `e : (fun m => conj (b m) * if m = n then (1 : ℂ) else 0) = fun m => if m = n then conj (b n) else 0`. Use function extensionality and compare the values at `m`.

Use `split_ifs with h`. Rewrite using `[h, mul_one]`. Rewrite using `[mul_zero]`. Rewrite using `[e]`. Conclude with `hasSum_ite_eq n (conj (b n))`.

Conclude with `hs.unique h2`. Establish `hB : HasSum (fun n => ∫ x in (0 : ℝ)..1, a n * (conj (G x) * ex n x)) (∫ x in (0 : ℝ)..1, conj (G x) * F x)`. Use `intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => ‖a n‖ * ∑' m, ‖b m‖) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `n`. Conclude with `(continuous_const.mul ((Complex.continuous_conj.comp hGc).mul (ex_cont n))).aestronglyMeasurable`.

Introduce `n`. Use `Filter.Eventually.of_forall (fun t _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul, ex_norm, mul_one, Complex.norm_conj]`. Conclude with `mul_le_mul_of_nonneg_left (hGb t) (norm_nonneg _)`. Conclude with `Filter.Eventually.of_forall (fun t _ => han.mul_right _)`.

Conclude with `intervalIntegrable_const`. Use `Filter.Eventually.of_forall (fun t _ => ?_)` and prove the remaining obligations. Establish `e : (fun n => a n * (conj (G t) * ex n t)) = fun n => conj (G t) * (a n * ex n t)`. Use function extensionality and compare the values at `n`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `(hF t).mul_left (conj (G t))`. Rewrite `hB` using `[intervalIntegral.integral_const_mul, hC]`. Establish `e : (fun n => conj (b n) * a n) = fun n => a n * conj (b n)`. Use function extensionality and compare the values at `n`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hB`.
-/
private theorem pars_abs (a b : ℕ → ℂ) (ha : Summable a) (hb : Summable b) (F G : ℝ → ℂ)
    (hF : ∀ x, HasSum (fun n => a n * ex n x) (F x)) (hG : ∀ x, HasSum (fun n => b n * ex n x) (G x)) :
    HasSum (fun n => conj (b n) * a n) (∫ x in (0 : ℝ)..1, conj (G x) * F x) := by
  have han : Summable (fun n => ‖a n‖) := summable_norm_iff.mpr ha
  have hbn : Summable (fun n => ‖b n‖) := summable_norm_iff.mpr hb
  have hGc : Continuous G := by
    have e : G = fun x => ∑' n, b n * ex n x := funext fun x => (hG x).tsum_eq.symm
    rw [e]
    refine continuous_tsum (fun n => continuous_const.mul (ex_cont n)) hbn ?_
    intro n x
    rw [norm_mul, ex_norm, mul_one]
  have hGb : ∀ t, ‖G t‖ ≤ ∑' n, ‖b n‖ := by
    intro t
    rw [← (hG t).tsum_eq]
    have e : (fun n => ‖b n * ex n t‖) = fun n => ‖b n‖ := by
      funext n
      rw [norm_mul, ex_norm, mul_one]
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
    · rw [e]; exact hbn
    · rw [e]
  have hC : ∀ n, ∫ x in (0 : ℝ)..1, conj (G x) * ex n x = conj (b n) := by
    intro n
    have hs : HasSum (fun m => ∫ x in (0 : ℝ)..1, conj (b m) * (conj (ex m x) * ex n x))
        (∫ x in (0 : ℝ)..1, conj (G x) * ex n x) := by
      refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun m _ => ‖b m‖)
        ?_ ?_ ?_ ?_ ?_
      · intro m
        exact (continuous_const.mul
          ((Complex.continuous_conj.comp (ex_cont m)).mul (ex_cont n))).aestronglyMeasurable
      · intro m
        refine Filter.Eventually.of_forall (fun t _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, ex_norm, ex_norm]
        simp
      · exact Filter.Eventually.of_forall (fun t _ => hbn)
      · exact intervalIntegrable_const
      · refine Filter.Eventually.of_forall (fun t _ => ?_)
        have e : (fun m => conj (b m) * (conj (ex m t) * ex n t)) =
            fun m => conj (b m * ex m t) * ex n t := by
          funext m
          rw [map_mul, mul_assoc]
        rw [e]
        exact (Complex.hasSum_conj'.mpr (hG t)).mul_right (ex n t)
    simp_rw [intervalIntegral.integral_const_mul, ex_orth] at hs
    have h2 : HasSum (fun m => conj (b m) * if m = n then (1 : ℂ) else 0) (conj (b n)) := by
      have e : (fun m => conj (b m) * if m = n then (1 : ℂ) else 0) =
          fun m => if m = n then conj (b n) else 0 := by
        funext m
        split_ifs with h
        · rw [h, mul_one]
        · rw [mul_zero]
      rw [e]
      exact hasSum_ite_eq n (conj (b n))
    exact hs.unique h2
  have hB : HasSum (fun n => ∫ x in (0 : ℝ)..1, a n * (conj (G x) * ex n x))
      (∫ x in (0 : ℝ)..1, conj (G x) * F x) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => ‖a n‖ * ∑' m, ‖b m‖) ?_ ?_ ?_ ?_ ?_
    · intro n
      exact (continuous_const.mul
        ((Complex.continuous_conj.comp hGc).mul (ex_cont n))).aestronglyMeasurable
    · intro n
      refine Filter.Eventually.of_forall (fun t _ => ?_)
      rw [norm_mul, norm_mul, ex_norm, mul_one, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (hGb t) (norm_nonneg _)
    · exact Filter.Eventually.of_forall (fun t _ => han.mul_right _)
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall (fun t _ => ?_)
      have e : (fun n => a n * (conj (G t) * ex n t)) = fun n => conj (G t) * (a n * ex n t) := by
        funext n
        ring
      rw [e]
      exact (hF t).mul_left (conj (G t))
  simp_rw [intervalIntegral.integral_const_mul, hC] at hB
  have e : (fun n => conj (b n) * a n) = fun n => a n * conj (b n) := by
    funext n
    ring
  rw [e]
  exact hB

/- English proof (translation)
Establish `hp : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 L)).strictPeriods`. Rewrite using `[CongruenceSubgroup.strictPeriods_Gamma1]`. Conclude with `AddSubgroup.mem_zmultiples 1`. Establish `hs` using `ModularForm.hasSum_qExpansion f one_pos hp (pt x y)`. Establish `him : 0 < ((x : ℂ) + y * Complex.I).im` using `by simp [hy]`.

Establish `hc : ((pt x y : ℍ) : ℂ) = x + y * Complex.I`. Unfold `pt`. Rewrite using `[UpperHalfPlane.ofComplex_apply_of_im_pos him]`. Establish `e : (fun n : ℕ => coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ) * ex n x) = fun m => (qExpansion 1 f).coeff m * Function.Periodic.qParam 1 ↑(pt x y) ^ m`. Use function extensionality and compare the values at `n`.

Rewrite using `[hc, mul_assoc]`. Unfold `coef ex Function.Periodic.qParam`. Use `congr 1`. Rewrite using `[← Complex.exp_nat_mul, Complex.ofReal_exp, ← Complex.exp_add]`. Use `congr 1`.

Use `push_cast`. Take the linear combination `(-(2 * (Real.pi : ℂ) * n * y)) * Complex.I_sq`. Rewrite using `[e]`. Conclude with `hs`.
-/
private theorem line_exp (k L : ℕ) [NeZero L] (f : CuspForm (Gamma1 L) (k : ℤ)) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun n : ℕ => coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ) * ex n x) (f (pt x y)) := by
  have hp : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 L)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples 1
  have hs := ModularForm.hasSum_qExpansion f one_pos hp (pt x y)
  have him : 0 < ((x : ℂ) + y * Complex.I).im := by simp [hy]
  have hc : ((pt x y : ℍ) : ℂ) = x + y * Complex.I := by
    unfold pt
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have e : (fun n : ℕ => coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ) * ex n x) =
      fun m => (qExpansion 1 f).coeff m * Function.Periodic.qParam 1 ↑(pt x y) ^ m := by
    funext n
    rw [hc, mul_assoc]
    unfold coef ex Function.Periodic.qParam
    congr 1
    rw [← Complex.exp_nat_mul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (-(2 * (Real.pi : ℂ) * n * y)) * Complex.I_sq
  rw [e]
  exact hs

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
/- English proof (translation)
Introduce `k L _ f g y hy`. Establish `hF` using `line_exp k L f y hy`. Establish `hG` using `line_exp k L g y hy`. Establish `ex0 : ∀ n, ex n 0 = 1`. Introduce `n`.

Simplify using `[ex]`. Establish `ha : Summable (fun n : ℕ => coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ))` using `(hF 0).summable.congr (fun n => by rw [ex0, mul_one])`. Establish `hb : Summable (fun n : ℕ => coef g n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ))` using `(hG 0).summable.congr (fun n => by rw [ex0, mul_one])`. Establish `h` using `pars_abs _ _ ha hb (fun x => f (pt x y)) (fun x => g (pt x y)) hF hG`. Establish `e : (fun n : ℕ => conj (coef g n) * coef f n * ((Real.exp (-(4 * Real.pi * n) * y) : ℝ) : ℂ)) = fun n => conj (coef g n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ)) * (coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ))`.

Use function extensionality and compare the values at `n`. Rewrite using `[map_mul, Complex.conj_ofReal, show -(4 * Real.pi * n) * y = (-(2 * Real.pi * n) * y) + (-(2 * Real.pi * n) * y) by ring, Real.exp_add]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `h`.
-/
theorem UpperTheory.V.Af.Rs.pars :
    UpperTheory.V.Af.Rs.Pars := by
  intro k L _ f g y hy
  have hF := line_exp k L f y hy
  have hG := line_exp k L g y hy
  have ex0 : ∀ n, ex n 0 = 1 := by
    intro n
    simp [ex]
  have ha : Summable (fun n : ℕ => coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ)) :=
    (hF 0).summable.congr (fun n => by rw [ex0, mul_one])
  have hb : Summable (fun n : ℕ => coef g n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ)) :=
    (hG 0).summable.congr (fun n => by rw [ex0, mul_one])
  have h := pars_abs _ _ ha hb (fun x => f (pt x y)) (fun x => g (pt x y)) hF hG
  have e : (fun n : ℕ => conj (coef g n) * coef f n * ((Real.exp (-(4 * Real.pi * n) * y) : ℝ) : ℂ)) =
      fun n => conj (coef g n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ)) *
        (coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ)) := by
    funext n
    rw [map_mul, Complex.conj_ofReal,
      show -(4 * Real.pi * n) * y = (-(2 * Real.pi * n) * y) + (-(2 * Real.pi * n) * y) by ring,
      Real.exp_add]
    push_cast
    ring
  rw [e]
  exact h
