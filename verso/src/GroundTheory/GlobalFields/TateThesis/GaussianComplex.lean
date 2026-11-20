import Mathlib
import GroundTheory.GlobalFields.TateThesis.Gaussian

namespace GroundTheory.Global

open Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform ENNReal

noncomputable section

def traceFormℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  (2 : ℝ) • (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.reCLM).comp (ContinuousLinearMap.mul ℝ ℂ)

/- English proof (translation)
Simplify using `[traceFormℂ]`.
-/
@[simp] theorem traceFormℂ_apply (z w : ℂ) : traceFormℂ z w = 2 * (z * w).re := by
  simp [traceFormℂ]

def complexPlaceMeasure : Measure ℂ := (2 : ℝ≥0∞) • volume

def complexFourier (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  ∫ z, 𝐞 (-(2 * (z * w).re)) • f z ∂complexPlaceMeasure

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `[complexFourier, VectorFourier.fourierIntegral]`.
-/
theorem complexFourier_eq_fourierIntegral (f : ℂ → ℂ) :
    complexFourier f =
      VectorFourier.fourierIntegral 𝐞 complexPlaceMeasure traceFormℂ.toLinearMap₁₂ f := by
  funext w
  simp [complexFourier, VectorFourier.fourierIntegral]

def complexGaussian (m : ℤ) (z : ℂ) : ℂ :=
  (if 0 ≤ m then z ^ m.natAbs else conj z ^ m.natAbs) * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)

/- English proof (translation)
Simplify using `[complexGaussian]`.
-/
theorem complexGaussian_zero (z : ℂ) :
    complexGaussian 0 z = Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
  simp [complexGaussian]

/- English proof (translation)
Rewrite using `[complexFourier, complexPlaceMeasure, integral_smul_measure, fourier_eq]`. Simplify using `only [ENNReal.toReal_ofNat, Complex.real_smul, ofReal_ofNat]`. Use `congr 2`. Use function extensionality and compare the values at `z`. Use `congr 3`.

Rewrite using `[Complex.inner]`. Simplify using `[Complex.mul_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem complexFourier_eq_two_mul_fourier (f : ℂ → ℂ) (w : ℂ) :
    complexFourier f w = 2 * 𝓕 f (2 * conj w) := by
  rw [complexFourier, complexPlaceMeasure, integral_smul_measure, fourier_eq]
  simp only [ENNReal.toReal_ofNat, Complex.real_smul, ofReal_ofNat]
  congr 2
  funext z
  congr 3
  rw [Complex.inner]
  simp [Complex.mul_re]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `w`. Rewrite using `[complexFourier_eq_two_mul_fourier]`. Establish `hb : 0 < ((2 * π : ℝ) : ℂ).re` using `by simp [Real.pi_pos]`. Establish `h` using `fourier_gaussian_innerProductSpace (V := ℂ) hb (2 * conj w)`. Establish `e : complexGaussian 0 = fun v : ℂ ↦ Complex.exp (-((2 * π : ℝ) : ℂ) * (‖v‖ : ℂ) ^ 2)`.

Use function extensionality and compare the values at `v`. Rewrite using `[complexGaussian_zero]`. Use `push_cast`. Put the polynomial expressions in normal form. Rewrite using `[e, h, Complex.finrank_real_complex]`.

Establish `hpi : (π : ℂ) ≠ 0` using `ofReal_ne_zero.mpr Real.pi_ne_zero`. Establish `hn : ‖2 * conj w‖ = 2 * ‖w‖` using `by simp`. Rewrite using `[hn]`. Establish `h1 : ((π : ℂ) / ((2 * π : ℝ) : ℂ)) ^ (((2 : ℕ) : ℂ) / 2) = 1 / 2`. Establish `: ((2 : ℕ) : ℂ) / 2 = 1` using `by norm_num`.

Rewrite using `[this, cpow_one]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h1]`. Use `push_cast`.

Rewrite using `[← mul_assoc, show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem complexFourier_complexGaussian_zero :
    complexFourier (complexGaussian 0) = complexGaussian 0 := by
  funext w
  rw [complexFourier_eq_two_mul_fourier]
  have hb : 0 < ((2 * π : ℝ) : ℂ).re := by simp [Real.pi_pos]
  have h := fourier_gaussian_innerProductSpace (V := ℂ) hb (2 * conj w)
  have e : complexGaussian 0 = fun v : ℂ ↦ Complex.exp (-((2 * π : ℝ) : ℂ) * (‖v‖ : ℂ) ^ 2) := by
    funext v; rw [complexGaussian_zero]; push_cast; ring_nf
  rw [e, h, Complex.finrank_real_complex]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn : ‖2 * conj w‖ = 2 * ‖w‖ := by simp
  rw [hn]
  have h1 : ((π : ℂ) / ((2 * π : ℝ) : ℂ)) ^ (((2 : ℕ) : ℂ) / 2) = 1 / 2 := by
    have : ((2 : ℕ) : ℂ) / 2 = 1 := by norm_num
    rw [this, cpow_one]; push_cast; field_simp
  rw [h1]
  push_cast
  rw [← mul_assoc, show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_mul]
  congr 1
  field_simp

/- English proof (translation)
Establish `h` using `(integrable_fun_norm_addHaar (volume : Measure ℂ) (f := fun y : ℝ ↦ y ^ k * Real.exp (-(2 * π) * y ^ 2))).2`. Use `h ?_` and prove the remaining obligations. Rewrite using `[Complex.finrank_real_complex]`. Establish `h2` using `integrableOn_rpow_mul_exp_neg_mul_sq (b := 2 * π) (by positivity) (s := ((k + 1 : ℕ) : ℝ)) (by have := Nat.cast_nonneg (α := ℝ) (k + 1); linarith)`. Use `h2.congr_fun (fun y _ ↦ ?_) measurableSet_Ioi` and prove the remaining obligations.

Simplify using `only [Real.rpow_natCast, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integrable_norm_pow_mul_exp_neg_two_pi_mul_sq (k : ℕ) :
    Integrable (fun z : ℂ ↦ ‖z‖ ^ k * Real.exp (-(2 * π) * ‖z‖ ^ 2)) := by
  have h := (integrable_fun_norm_addHaar (volume : Measure ℂ)
    (f := fun y : ℝ ↦ y ^ k * Real.exp (-(2 * π) * y ^ 2))).2
  refine h ?_
  rw [Complex.finrank_real_complex]
  have h2 := integrableOn_rpow_mul_exp_neg_mul_sq (b := 2 * π) (by positivity)
    (s := ((k + 1 : ℕ) : ℝ)) (by have := Nat.cast_nonneg (α := ℝ) (k + 1); linarith)
  refine h2.congr_fun (fun y _ ↦ ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, smul_eq_mul]
  ring

/- English proof (translation)
Use `(integrable_norm_pow_mul_exp_neg_two_pi_mul_sq (k + m.natAbs)).mono' ?_ ?_` and prove the remaining obligations. Use `Continuous.aestronglyMeasurable ?_` and prove the remaining obligations. Unfold `complexGaussian`. Apply the tactic sequence `split_ifs <;> fun_prop`. Use `Filter.Eventually.of_forall fun z ↦ ?_` and prove the remaining obligations.

Rewrite using `[norm_smul, complexGaussian, norm_mul, norm_exp]`. Establish `: (-2 * π * (‖z‖ : ℂ) ^ 2).re = -(2 * π) * ‖z‖ ^ 2`. Rewrite using `[← ofReal_pow, ← ofReal_ofNat, ← ofReal_neg, ← ofReal_mul, ← ofReal_mul, ofReal_re]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Apply the tactic sequence `split_ifs <;> simp [pow_add, mul_assoc]`.
-/
theorem integrable_norm_pow_smul_complexGaussian (m : ℤ) (k : ℕ) :
    Integrable (fun z : ℂ ↦ (‖z‖ ^ k : ℝ) • complexGaussian m z) := by
  refine (integrable_norm_pow_mul_exp_neg_two_pi_mul_sq (k + m.natAbs)).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    unfold complexGaussian
    split_ifs <;> fun_prop
  · refine Filter.Eventually.of_forall fun z ↦ ?_
    rw [norm_smul, complexGaussian, norm_mul, norm_exp]
    have : (-2 * π * (‖z‖ : ℂ) ^ 2).re = -(2 * π) * ‖z‖ ^ 2 := by
      rw [← ofReal_pow, ← ofReal_ofNat, ← ofReal_neg, ← ofReal_mul, ← ofReal_mul, ofReal_re]
      ring
    rw [this]
    split_ifs <;> simp [pow_add, mul_assoc]

/- English proof (translation)
The claim follows from `(integrable_norm_pow_smul_complexGaussian m k).smul_measure (by simp)`.
-/
theorem integrable_norm_pow_smul_complexGaussian' (m : ℤ) (k : ℕ) :
    Integrable (fun z : ℂ ↦ (‖z‖ ^ k : ℝ) • complexGaussian m z) complexPlaceMeasure :=
  (integrable_norm_pow_smul_complexGaussian m k).smul_measure (by simp)

/- English proof (translation)
Simplify using `using integrable_norm_pow_smul_complexGaussian' m 0`.
-/
theorem integrable_complexGaussian (m : ℤ) :
    Integrable (complexGaussian m) complexPlaceMeasure := by
  simpa using integrable_norm_pow_smul_complexGaussian' m 0

/- English proof (translation)
Establish `hn : (‖z‖ : ℂ) ≠ 0` using `by simpa using hz`. Rewrite using `[complexGaussian]`. Use `split_ifs with hm`. Take `⟨n, rfl⟩` from `Int.eq_ofNat_of_zero_le hm`. Simplify using `only [Int.natAbs_natCast, zpow_neg, zpow_natCast, div_pow]`.

Clear the denominators using the available nonvanishing facts. Take `⟨n, hn'⟩ : ∃ n : ℕ, m = -(n : ℤ)` from `⟨m.natAbs, by omega⟩`. Substitute `hn'` using the available equality. Simplify using `only [Int.natAbs_neg, Int.natAbs_natCast, neg_neg, zpow_natCast, div_pow]`. Establish `hc : conj z * z = (‖z‖ : ℂ) ^ 2`.

Rewrite using `[mul_comm, mul_conj, normSq_eq_norm_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `: conj z ^ n * z ^ n = (‖z‖ : ℂ) ^ n * (‖z‖ : ℂ) ^ n`. Rewrite using `[← mul_pow, hc, ← pow_mul, ← pow_add]`.

Put the polynomial expressions in normal form. Clear the denominators using the available nonvanishing facts. Take the linear combination `this`.
-/
theorem complexGaussian_mul_zpow {z : ℂ} (hz : z ≠ 0) (m : ℤ) :
    complexGaussian m z * (z / (‖z‖ : ℂ)) ^ (-m) =
      (‖z‖ : ℂ) ^ m.natAbs * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
  have hn : (‖z‖ : ℂ) ≠ 0 := by simpa using hz
  rw [complexGaussian]
  split_ifs with hm
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    simp only [Int.natAbs_natCast, zpow_neg, zpow_natCast, div_pow]
    field_simp
  · obtain ⟨n, hn'⟩ : ∃ n : ℕ, m = -(n : ℤ) := ⟨m.natAbs, by omega⟩
    subst hn'
    simp only [Int.natAbs_neg, Int.natAbs_natCast, neg_neg, zpow_natCast, div_pow]
    have hc : conj z * z = (‖z‖ : ℂ) ^ 2 := by
      rw [mul_comm, mul_conj, normSq_eq_norm_sq]; push_cast; ring
    have : conj z ^ n * z ^ n = (‖z‖ : ℂ) ^ n * (‖z‖ : ℂ) ^ n := by
      rw [← mul_pow, hc, ← pow_mul, ← pow_add]; ring_nf
    field_simp
    linear_combination this

/- English proof (translation)
Rewrite using `[complexPlaceMeasure, integral_smul_measure, integral_fun_norm_addHaar volume f, Complex.finrank_real_complex]`. Establish `hb : (volume : Measure ℂ).real (Metric.ball 0 1) = π`. Simplify using `[Measure.real, Complex.volume_ball]`. Rewrite using `[hb]`. Simplify using `only [ENNReal.toReal_ofNat, pow_one, Complex.real_smul, nsmul_eq_mul, Nat.cast_ofNat, Nat.add_one_sub_one]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_comp_norm_complexPlaceMeasure (f : ℝ → ℂ) :
    ∫ z, f ‖z‖ ∂complexPlaceMeasure = 4 * π * ∫ y in Ioi (0 : ℝ), (y : ℂ) * f y := by
  rw [complexPlaceMeasure, integral_smul_measure, integral_fun_norm_addHaar volume f,
    Complex.finrank_real_complex]
  have hb : (volume : Measure ℂ).real (Metric.ball 0 1) = π := by
    simp [Measure.real, Complex.volume_ball]
  rw [hb]
  simp only [ENNReal.toReal_ofNat, pow_one, Complex.real_smul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.add_one_sub_one]
  push_cast
  ring

/- English proof (translation)
Use `set n := m.natAbs with hn`. Establish `h : (fun z : ℂ ↦ complexGaussian m z * (z / (‖z‖ : ℂ)) ^ (-m) * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s / ((‖z‖ ^ 2 : ℝ) : ℂ)) = fun z ↦ (fun y : ℝ ↦ (y : ℂ) ^ n * ((Real.exp (-(2 * π * y ^ 2)) : ℝ) : ℂ) * ((y ^ 2 : ℝ) : ℂ) ^ s / ((y ^ 2 : ℝ) : ℂ)) ‖z‖`. Use function extensionality and compare the values at `z`. Distinguish the cases in `hz : z = 0`. Substitute `hz` using the available equality.

Simplify using the standard rewrite rules. Simplify using `only`. Rewrite using `[complexGaussian_mul_zpow hz, ofReal_exp, ← hn]`. Use `push_cast`. Put the polynomial expressions in normal form.

Rewrite using `[h, integral_comp_norm_complexPlaceMeasure (fun y : ℝ ↦ (y : ℂ) ^ n * ((Real.exp (-(2 * π * y ^ 2)) : ℝ) : ℂ) * ((y ^ 2 : ℝ) : ℂ) ^ s / ((y ^ 2 : ℝ) : ℂ))]`. Establish `ha : 0 < (2 * s + n).re` using `by simp; linarith`. Establish `: ∫ y in Ioi (0 : ℝ), (y : ℂ) * ((y : ℂ) ^ n * ((Real.exp (-(2 * π * y ^ 2)) : ℝ) : ℂ) * ((y ^ 2 : ℝ) : ℂ) ^ s / ((y ^ 2 : ℝ) : ℂ)) = mellin (fun t : ℝ ↦ ((Real.exp (-(2 * π * t ^ 2)) : ℝ) : ℂ)) (2 * s + n)`. Rewrite using `[mellin]`. Use `setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_` and prove the remaining obligations.

Establish `hy0 : (y : ℂ) ≠ 0` using `ofReal_ne_zero.mpr (ne_of_gt hy)`. Establish `e1 : ((y ^ 2 : ℝ) : ℂ) ^ s = (y : ℂ) ^ (((2 : ℝ) : ℂ) * s)`. Rewrite using `[cpow_mul_ofReal_nonneg (le_of_lt hy), Real.rpow_two]`. Establish `e2 : (y : ℂ) ^ (2 * s + n - 1) = (y : ℂ) ^ (((2 : ℝ) : ℂ) * s) * (y : ℂ) ^ n / y`. Rewrite using `[cpow_sub _ _ hy0, cpow_add _ _ hy0, cpow_natCast, cpow_one]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, smul_eq_mul]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this, mellin_exp_neg_mul_sq (by positivity) ha, Gammaℂ_def]`. Establish `e3 : (2 * s + n) / 2 = s + n / 2` using `by ring`. Rewrite using `[e3]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_complexGaussian_mul_zpow_mul_cpow (m : ℤ) {s : ℂ}
    (hs : 0 < s.re + m.natAbs / 2) :
    ∫ z, complexGaussian m z * (z / (‖z‖ : ℂ)) ^ (-m) * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s /
        ((‖z‖ ^ 2 : ℝ) : ℂ) ∂complexPlaceMeasure =
      π * Gammaℂ (s + m.natAbs / 2) := by
  set n := m.natAbs with hn
  have h : (fun z : ℂ ↦ complexGaussian m z * (z / (‖z‖ : ℂ)) ^ (-m) *
        ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s / ((‖z‖ ^ 2 : ℝ) : ℂ)) =
      fun z ↦ (fun y : ℝ ↦ (y : ℂ) ^ n * ((Real.exp (-(2 * π * y ^ 2)) : ℝ) : ℂ) *
        ((y ^ 2 : ℝ) : ℂ) ^ s / ((y ^ 2 : ℝ) : ℂ)) ‖z‖ := by
    funext z
    by_cases hz : z = 0
    · subst hz; simp
    · simp only
      rw [complexGaussian_mul_zpow hz, ofReal_exp, ← hn]
      push_cast
      ring_nf
  rw [h, integral_comp_norm_complexPlaceMeasure (fun y : ℝ ↦ (y : ℂ) ^ n *
    ((Real.exp (-(2 * π * y ^ 2)) : ℝ) : ℂ) * ((y ^ 2 : ℝ) : ℂ) ^ s / ((y ^ 2 : ℝ) : ℂ))]
  have ha : 0 < (2 * s + n).re := by simp; linarith
  have : ∫ y in Ioi (0 : ℝ), (y : ℂ) * ((y : ℂ) ^ n * ((Real.exp (-(2 * π * y ^ 2)) : ℝ) : ℂ) *
        ((y ^ 2 : ℝ) : ℂ) ^ s / ((y ^ 2 : ℝ) : ℂ)) =
      mellin (fun t : ℝ ↦ ((Real.exp (-(2 * π * t ^ 2)) : ℝ) : ℂ)) (2 * s + n) := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hy)
    have e1 : ((y ^ 2 : ℝ) : ℂ) ^ s = (y : ℂ) ^ (((2 : ℝ) : ℂ) * s) := by
      rw [cpow_mul_ofReal_nonneg (le_of_lt hy), Real.rpow_two]
    have e2 : (y : ℂ) ^ (2 * s + n - 1) = (y : ℂ) ^ (((2 : ℝ) : ℂ) * s) * (y : ℂ) ^ n / y := by
      rw [cpow_sub _ _ hy0, cpow_add _ _ hy0, cpow_natCast, cpow_one]; push_cast; ring
    rw [e1, e2, smul_eq_mul]
    push_cast
    field_simp
  rw [this, mellin_exp_neg_mul_sq (by positivity) ha, Gammaℂ_def]
  have e3 : (2 * s + n) / 2 = s + n / 2 := by ring
  rw [e3]
  push_cast
  ring

end

end GroundTheory.Global
