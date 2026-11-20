import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierTransformMatrixSpaceInvolution

noncomputable section

open MeasureTheory Ad3.K Ad3.K.QuadraticBaseChangeGL3.Th ComplexConjugate

namespace GlobalTheory.CompanionTheory.RealWeil

def ee (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

/- English proof (translation)
Unfold `ee`. Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/- English proof (translation)
Simplify using `[ee]`.
-/
@[simp] theorem ee_zero : ee 0 = 1 := by simp [ee]

/- English proof (translation)
Unfold `ee`. Establish `: (2 * Real.pi * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Complex.norm_exp_ofReal_mul_I]`.
-/
theorem norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  have : (2 * Real.pi * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Unfold `ee`. Use `fun_prop`.
-/
theorem continuous_ee : Continuous ee := by
  unfold ee
  fun_prop

def Fr (Φ : ℂ → ℂ) (z : ℂ) : ℂ := ∫ u, ee (2 * (conj z * u).re) * Φ u ∂volC

/- English proof (translation)
Simplify using `only [rWR, if_true, ee]`.
-/
theorem rWR_zero (a b d : ℝ) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR a b 0 d Φ z = ee (a * b * Complex.normSq z) * sgR a * ((|a| : ℝ) : ℂ) * Φ ((a : ℂ) * z) := by
  simp only [rWR, if_true, ee]

/- English proof (translation)
Simplify using `only [rWR, if_neg hc, ee]`.
-/
theorem rWR_ne (a b d : ℝ) {c : ℝ} (hc : c ≠ 0) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR a b c d Φ z = Complex.I * sgR (-c) * ((|c|⁻¹ : ℝ) : ℂ) *
      ∫ u, ee ((a * Complex.normSq z + d * Complex.normSq u - 2 * (conj z * u).re) / c) * Φ u ∂volC := by
  simp only [rWR, if_neg hc, ee]

/- English proof (translation)
Rewrite using `[rWR_ne a b d hc, Fr, ← integral_const_mul (μ := volC) (ee (a / c * Complex.normSq z))]`. Use `congr 1`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Establish `e : (a * Complex.normSq z + d * Complex.normSq u - 2 * (conj z * u).re) / c = a / c * Complex.normSq z + (2 * (conj (((-c⁻¹ : ℝ) : ℂ) * z) * u).re + d / c * Complex.normSq u)`. Establish `: (conj (((-c⁻¹ : ℝ) : ℂ) * z) * u).re = -c⁻¹ * (conj z * u).re`.

Rewrite using `[map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `show ee _ * Φ u = ee _ * (ee _ * (ee _ * Φ u))`.

Rewrite using `[e, ee_add, ee_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rWR_fr (a b d : ℝ) {c : ℝ} (hc : c ≠ 0) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR a b c d Φ z = Complex.I * sgR (-c) * ((|c|⁻¹ : ℝ) : ℂ) * (ee (a / c * Complex.normSq z) *
      Fr (fun u => ee (d / c * Complex.normSq u) * Φ u) (((-c⁻¹ : ℝ) : ℂ) * z)) := by
  rw [rWR_ne a b d hc, Fr, ← integral_const_mul (μ := volC) (ee (a / c * Complex.normSq z))]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have e : (a * Complex.normSq z + d * Complex.normSq u - 2 * (conj z * u).re) / c =
      a / c * Complex.normSq z + (2 * (conj (((-c⁻¹ : ℝ) : ℂ) * z) * u).re + d / c * Complex.normSq u) := by
    have : (conj (((-c⁻¹ : ℝ) : ℂ) * z) * u).re = -c⁻¹ * (conj z * u).re := by
      rw [map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
    rw [this]
    field_simp
    ring
  show ee _ * Φ u = ee _ * (ee _ * (ee _ * Φ u))
  rw [e, ee_add, ee_add]
  ring

/- English proof (translation)
Rewrite using `[volC, integral_smul_measure]`. Simplify using the standard rewrite rules.
-/
theorem integral_volC (f : ℂ → ℂ) : ∫ u, f u ∂volC = 2 * ∫ u, f u := by
  rw [volC, integral_smul_measure]
  simp

/- English proof (translation)
Establish `h` using `Measure.integral_comp_smul (volume : Measure ℂ) f s`. Simplify using `only [Complex.real_smul, Complex.finrank_real_complex] at h`. Rewrite using `[integral_volC, integral_volC, h, abs_of_pos (by positivity : 0 < (s ^ 2)⁻¹)]`. Put the polynomial expressions in normal form.
-/
theorem integral_volC_smul (f : ℂ → ℂ) {s : ℝ} (hs : s ≠ 0) :
    ∫ u, f ((s : ℂ) * u) ∂volC = (((s ^ 2)⁻¹ : ℝ) : ℂ) * ∫ u, f u ∂volC := by
  have h := Measure.integral_comp_smul (volume : Measure ℂ) f s
  simp only [Complex.real_smul, Complex.finrank_real_complex] at h
  rw [integral_volC, integral_volC, h, abs_of_pos (by positivity : 0 < (s ^ 2)⁻¹)]
  ring_nf

/- English proof (translation)
Break down `lt_or_gt_of_ne ha with h1 | h1` into its components or cases. Simplify using `[sgR, h1.le.not_gt, abs_of_neg h1]`. Simplify using `[sgR, h1, abs_of_pos h1]`.
-/
theorem sgR_mul_abs {a : ℝ} (ha : a ≠ 0) : sgR a * ((|a| : ℝ) : ℂ) = (a : ℂ) := by
  rcases lt_or_gt_of_ne ha with h1 | h1
  · simp [sgR, h1.le.not_gt, abs_of_neg h1]
  · simp [sgR, h1, abs_of_pos h1]

/- English proof (translation)
Break down `lt_or_gt_of_ne ha with h1 | h1` into its components or cases. Simplify using `[sgR, h1.le.not_gt, abs_of_neg h1]`. Simplify using `[sgR, h1, abs_of_pos h1]`.
-/
theorem sgR_mul_abs_inv {a : ℝ} (ha : a ≠ 0) : sgR a * ((|a|⁻¹ : ℝ) : ℂ) = ((a⁻¹ : ℝ) : ℂ) := by
  rcases lt_or_gt_of_ne ha with h1 | h1
  · simp [sgR, h1.le.not_gt, abs_of_neg h1]
  · simp [sgR, h1, abs_of_pos h1]

def Gs (ε t : ℝ) (w : ℂ) : ℂ :=
  (2 * Real.pi / ((ε : ℂ) - 2 * Real.pi * t * Complex.I)) *
    Complex.exp (-(4 * Real.pi ^ 2 * (Complex.normSq w : ℂ)) / ((ε : ℂ) - 2 * Real.pi * t * Complex.I))

open Filter Topology
open scoped FourierTransform

/- English proof (translation)
Take `⟨f, rfl⟩` from `hΦ`. Conclude with `⟨k • f, by funext z; simp⟩`.
-/
theorem const_mem (k : ℂ) {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) : (fun z => k * Φ z) ∈ SchC := by
  obtain ⟨f, rfl⟩ := hΦ
  exact ⟨k • f, by funext z; simp⟩

/- English proof (translation)
Take `⟨f, rfl⟩` from `hΦ`. Set `L : ℂ ≃L[ℝ] ℂ` to `ContinuousLinearEquiv.smulLeft (Units.mk0 s hs)`. Use `⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Simplify using `[L, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]`.
-/
theorem dil_mem {s : ℝ} (hs : s ≠ 0) {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) : (fun z => Φ ((s : ℂ) * z)) ∈ SchC := by
  obtain ⟨f, rfl⟩ := hΦ
  let L : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 s hs)
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f, ?_⟩
  funext z
  simp [L, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/- English proof (translation)
Take `⟨f, rfl⟩` from `hΦ`. Use `⟨GlobalTheory.CompanionTheory.Kloc.Fresnel.chirpS t f, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Rewrite using `[GlobalTheory.CompanionTheory.Kloc.Fresnel.chirpS_apply]`. Use `congr 1`.

Simplify using `only [GlobalTheory.CompanionTheory.Kloc.Fresnel.chirp, ee]`. Rewrite using `[Complex.normSq_eq_norm_sq]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chirp_mem (t : ℝ) {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) : (fun z => ee (t * Complex.normSq z) * Φ z) ∈ SchC := by
  obtain ⟨f, rfl⟩ := hΦ
  refine ⟨GlobalTheory.CompanionTheory.Kloc.Fresnel.chirpS t f, ?_⟩
  funext z
  rw [GlobalTheory.CompanionTheory.Kloc.Fresnel.chirpS_apply]
  congr 1
  simp only [GlobalTheory.CompanionTheory.Kloc.Fresnel.chirp, ee]
  rw [Complex.normSq_eq_norm_sq]
  congr 1
  push_cast
  ring

/- English proof (translation)
Rewrite using `[Complex.inner]`. Simplify using `only [Complex.mul_re, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inner_eq (v z : ℂ) : inner ℝ v z = (conj z * v).re := by
  rw [Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/- English proof (translation)
Rewrite using `[Fr, integral_volC, Real.fourier_eq']`. Use `congr 1`. Use `integral_congr_ae (Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Simplify using `only [ee, smul_eq_mul]`. Use `congr 2`.

Establish `h : inner ℝ v (((-2 : ℝ) : ℂ) * z) = -2 * (conj z * v).re`. Rewrite using `[inner_eq, map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]`. Rewrite using `[h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Fr_eq (Φ : ℂ → ℂ) (z : ℂ) : Fr Φ z = 2 * 𝓕 Φ (((-2 : ℝ) : ℂ) * z) := by
  rw [Fr, integral_volC, Real.fourier_eq']
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [ee, smul_eq_mul]
  congr 2
  have h : inner ℝ v (((-2 : ℝ) : ℂ) * z) = -2 * (conj z * v).re := by
    rw [inner_eq, map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
  rw [h]
  push_cast
  ring

/- English proof (translation)
Take `⟨f, rfl⟩` from `hΦ`. Establish `e : Fr ⇑f = fun z => 2 * 𝓕 (⇑f) (((-2 : ℝ) : ℂ) * z)` using `funext (Fr_eq _)`. Rewrite using `[e]`. Conclude with `const_mem 2 (dil_mem (by norm_num) ⟨(𝓕 f : SchwartzMap ℂ ℂ), SchwartzMap.fourier_coe f⟩)`.
-/
theorem Fr_mem {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) : Fr Φ ∈ SchC := by
  obtain ⟨f, rfl⟩ := hΦ
  have e : Fr ⇑f = fun z => 2 * 𝓕 (⇑f) (((-2 : ℝ) : ℂ) * z) := funext (Fr_eq _)
  rw [e]
  exact const_mem 2 (dil_mem (by norm_num) ⟨(𝓕 f : SchwartzMap ℂ ℂ), SchwartzMap.fourier_coe f⟩)

/- English proof (translation)
Take `⟨f, rfl⟩` from `hΦ`. Establish `e : Fr ⇑f = fun z => 2 * 𝓕 (⇑f) (((-2 : ℝ) : ℂ) * z)` using `funext (Fr_eq _)`. Establish `hint : Integrable (𝓕 (f : ℂ → ℂ))`. Use `(𝓕 f).integrable (μ := volume)` as an intermediate fact. Rewrite `this` using `[SchwartzMap.fourier_coe]`. Then use the resulting hypothesis.

Establish `hinv` using `congrFun (Continuous.fourierInv_fourier_eq f.continuous (f.integrable (μ := volume)) hint) (-z)`. Rewrite `hinv` using `[Real.fourierInv_eq']`. Rewrite using `[← hinv, e, Fr]`. Use `set k : ℂ → ℂ := fun v => ee (-(conj z * v).re) * (2 * 𝓕 (⇑f) v) with hk`. Establish `h` using `integral_volC_smul k (by norm_num : (-2 : ℝ) ≠ 0)`.

Establish `h1 : ∫ u, ee (2 * (conj z * u).re) * (2 * 𝓕 (⇑f) (((-2 : ℝ) : ℂ) * u)) ∂volC = ∫ u, k (((-2 : ℝ) : ℂ) * u) ∂volC`. Use `integral_congr_ae (Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Simplify using `only [hk]`. Use `congr 2`. Rewrite using `[mul_left_comm, Complex.re_ofReal_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, h, integral_volC, ← mul_assoc]`. Establish `h2 : (((((-2 : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * 2) = 2⁻¹`. Use `push_cast`. Evaluate the numerical expressions.

Rewrite using `[h2, hk]`. Simplify using `only []`. Establish `h3 : ∀ v : ℂ, ee (-(conj z * v).re) * (2 * 𝓕 (⇑f) v) = 2 * (Complex.exp (((2 * Real.pi * inner ℝ v (-z) : ℝ) : ℂ) * Complex.I) • 𝓕 (⇑f) v)`. Introduce `v`. Establish `: inner ℝ v (-z) = -(conj z * v).re`.

Rewrite using `[inner_neg_right, inner_eq]`. Rewrite using `[this, ee, smul_eq_mul]`. Establish `e4 : 2 * (Real.pi : ℂ) * Complex.I * ((-(conj z * v).re : ℝ) : ℂ) = ((2 * Real.pi * -(conj z * v).re : ℝ) : ℂ) * Complex.I`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e4]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h3]`. Rewrite using `[integral_const_mul]`. Simplify using the standard rewrite rules.
-/
theorem Fr_Fr {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) (z : ℂ) : Fr (Fr Φ) z = Φ (-z) := by
  obtain ⟨f, rfl⟩ := hΦ
  have e : Fr ⇑f = fun z => 2 * 𝓕 (⇑f) (((-2 : ℝ) : ℂ) * z) := funext (Fr_eq _)
  have hint : Integrable (𝓕 (f : ℂ → ℂ)) := by
    have := (𝓕 f).integrable (μ := volume)
    rwa [SchwartzMap.fourier_coe] at this
  have hinv := congrFun (Continuous.fourierInv_fourier_eq f.continuous (f.integrable (μ := volume)) hint) (-z)
  rw [Real.fourierInv_eq'] at hinv
  rw [← hinv, e, Fr]
  set k : ℂ → ℂ := fun v => ee (-(conj z * v).re) * (2 * 𝓕 (⇑f) v) with hk
  have h := integral_volC_smul k (by norm_num : (-2 : ℝ) ≠ 0)
  have h1 : ∫ u, ee (2 * (conj z * u).re) * (2 * 𝓕 (⇑f) (((-2 : ℝ) : ℂ) * u)) ∂volC = ∫ u, k (((-2 : ℝ) : ℂ) * u) ∂volC := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hk]
    congr 2
    rw [mul_left_comm, Complex.re_ofReal_mul]
    ring
  rw [h1, h, integral_volC, ← mul_assoc]
  have h2 : (((((-2 : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * 2) = 2⁻¹ := by
    push_cast
    norm_num
  rw [h2, hk]
  simp only []
  have h3 : ∀ v : ℂ, ee (-(conj z * v).re) * (2 * 𝓕 (⇑f) v) = 2 * (Complex.exp (((2 * Real.pi * inner ℝ v (-z) : ℝ) : ℂ) * Complex.I) • 𝓕 (⇑f) v) := by
    intro v
    have : inner ℝ v (-z) = -(conj z * v).re := by
      rw [inner_neg_right, inner_eq]
    rw [this, ee, smul_eq_mul]
    have e4 : 2 * (Real.pi : ℂ) * Complex.I * ((-(conj z * v).re : ℝ) : ℂ) = ((2 * Real.pi * -(conj z * v).re : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [e4]
    ring
  simp only [h3]
  rw [integral_const_mul]
  simp

/- English proof (translation)
Use `set b : ℂ := (ε : ℂ) - 2 * Real.pi * t * Complex.I with hbd`. Establish `hb : 0 < b.re` using `by simpa [hbd] using hε`. Establish `hb0 : b ≠ 0`. Introduce `h`. Rewrite `hb` using `[h]`.

Simplify using `at hb`. Establish `h` using `fourier_gaussian_innerProductSpace (V := ℂ) hb (((-2 : ℝ) : ℂ) * w)`. Establish `e1 : ∫ y, Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) * ee (t * Complex.normSq y + 2 * (conj w * y).re) ∂volC = Fr (fun v : ℂ => Complex.exp (-b * (‖v‖ : ℂ) ^ 2)) w`. Rewrite using `[Fr]`. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations.

Use `show Complex.exp _ * ee _ = ee _ * Complex.exp _`. Rewrite using `[ee_add]`. Simplify using `only [ee]`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, Complex.normSq_eq_norm_sq, hbd]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, Fr_eq, h, Gs, ← hbd]`. Simplify using `only [Complex.finrank_real_complex]`. Establish `e2 : (((2 : ℕ) : ℂ) / 2) = 1` using `by norm_num`.

Rewrite using `[e2, Complex.cpow_one, norm_mul, Complex.normSq_eq_norm_sq]`. Establish `e3 : ‖((-2 : ℝ) : ℂ)‖ = 2` using `by simp`. Rewrite using `[e3]`. Rewrite using `[← mul_assoc]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gauss_int (ε t : ℝ) (hε : 0 < ε) (w : ℂ) :
    ∫ y, Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) * ee (t * Complex.normSq y + 2 * (conj w * y).re) ∂volC = Gs ε t w := by
  set b : ℂ := (ε : ℂ) - 2 * Real.pi * t * Complex.I with hbd
  have hb : 0 < b.re := by simpa [hbd] using hε
  have hb0 : b ≠ 0 := by
    intro h
    rw [h] at hb
    simp at hb
  have h := fourier_gaussian_innerProductSpace (V := ℂ) hb (((-2 : ℝ) : ℂ) * w)
  have e1 : ∫ y, Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) * ee (t * Complex.normSq y + 2 * (conj w * y).re) ∂volC =
      Fr (fun v : ℂ => Complex.exp (-b * (‖v‖ : ℂ) ^ 2)) w := by
    rw [Fr]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show Complex.exp _ * ee _ = ee _ * Complex.exp _
    rw [ee_add]
    simp only [ee]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, Complex.normSq_eq_norm_sq, hbd]
    congr 1
    push_cast
    ring
  rw [e1, Fr_eq, h, Gs, ← hbd]
  simp only [Complex.finrank_real_complex]
  have e2 : (((2 : ℕ) : ℂ) / 2) = 1 := by norm_num
  rw [e2, Complex.cpow_one, norm_mul, Complex.normSq_eq_norm_sq]
  have e3 : ‖((-2 : ℝ) : ℂ)‖ = 2 := by simp
  rw [e3]
  rw [← mul_assoc]
  congr 1
  · ring
  · congr 1
    push_cast
    ring

/- English proof (translation)
Establish `hΨi : Integrable Ψ volC`. Take `⟨f, rfl⟩` from `hΨ`. Establish `h : Integrable (⇑f) (volume : Measure ℂ)` using `f.integrable`. Conclude with `h.smul_measure (by simp)`. Establish `hΨc : Continuous Ψ`.

Take `⟨f, rfl⟩` from `hΨ`. Conclude with `f.continuous`. Use `haveI : SFinite volC := by`. Unfold `volC`. Use `infer_instance`.

Establish `hF : Integrable (Function.uncurry fun (y u : ℂ) => K y * ee (2 * (conj (z + u) * y).re) * Ψ u) (volC.prod volC)`. Establish `base` using `Integrable.mul_prod hK hΨi`. Use `base.mono ?_ (Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Apply `Continuous.aestronglyMeasurable` to reduce the goal to its premises. Use `continuous_ee` as an intermediate fact.

Simplify using `only [Function.uncurry_def]`. Use `fun_prop`. Simplify using `only [Function.uncurry_def, norm_mul, norm_ee, mul_one, le_refl]`. Establish `hsw` using `integral_integral_swap hF`. Combine the equalities or inequalities in the displayed calculation.

Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Use `show _ * _ * (∫ u, _ ∂volC) = _`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Use `show _ = K y * ee _ * Ψ u`.

Establish `e : 2 * (conj (z + u) * y).re = 2 * (conj z * y).re + 2 * (conj y * u).re`. Simplify using `only [map_add, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ee_add]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = ∫ u, ∫ y, K y * ee (2 * (conj (z + u) * y).re) * Ψ u ∂volC ∂volC := hsw`. Use `_ = _ := by`. Use `integral_congr_ae (Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Conclude with `integral_mul_const _ _`.
-/
theorem fubini_Fr {K Ψ : ℂ → ℂ} (hK : Integrable K volC) (hKc : Continuous K) (hΨ : Ψ ∈ SchC) (z : ℂ) :
    ∫ y, K y * ee (2 * (conj z * y).re) * Fr Ψ y ∂volC =
      ∫ u, (∫ y, K y * ee (2 * (conj (z + u) * y).re) ∂volC) * Ψ u ∂volC := by
  have hΨi : Integrable Ψ volC := by
    obtain ⟨f, rfl⟩ := hΨ
    have h : Integrable (⇑f) (volume : Measure ℂ) := f.integrable
    exact h.smul_measure (by simp)
  have hΨc : Continuous Ψ := by
    obtain ⟨f, rfl⟩ := hΨ
    exact f.continuous
  haveI : SFinite volC := by
    unfold volC
    infer_instance
  have hF : Integrable (Function.uncurry fun (y u : ℂ) => K y * ee (2 * (conj (z + u) * y).re) * Ψ u) (volC.prod volC) := by
    have base := Integrable.mul_prod hK hΨi
    refine base.mono ?_ (Eventually.of_forall fun p => ?_)
    · apply Continuous.aestronglyMeasurable
      have := continuous_ee
      simp only [Function.uncurry_def]
      fun_prop
    · simp only [Function.uncurry_def, norm_mul, norm_ee, mul_one, le_refl]
  have hsw := integral_integral_swap hF
  calc _ = ∫ y, ∫ u, K y * ee (2 * (conj (z + u) * y).re) * Ψ u ∂volC ∂volC := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        show _ * _ * (∫ u, _ ∂volC) = _
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        show _ = K y * ee _ * Ψ u
        have e : 2 * (conj (z + u) * y).re = 2 * (conj z * y).re + 2 * (conj y * u).re := by
          simp only [map_add, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
          ring
        rw [e, ee_add]
        ring
    _ = ∫ u, ∫ y, K y * ee (2 * (conj (z + u) * y).re) * Ψ u ∂volC ∂volC := hsw
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        exact integral_mul_const _ _

/- English proof (translation)
Rewrite using `[Complex.norm_exp]`. Use `Real.exp_le_one_iff.2 ?_` and prove the remaining obligations. Use `Complex.normSq_nonneg y` as an intermediate fact. Simplify using `only [Complex.neg_re, Complex.ofReal_re]`. Establish `: 0 ≤ ε * Complex.normSq y` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_exp_reg_le {ε : ℝ} (hε : 0 < ε) (y : ℂ) : ‖Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  refine Real.exp_le_one_iff.2 ?_
  have := Complex.normSq_nonneg y
  simp only [Complex.neg_re, Complex.ofReal_re]
  have : 0 ≤ ε * Complex.normSq y := by positivity
  linarith

/- English proof (translation)
Establish `hs` using `Complex.continuous_normSq`. Use `tendsto_integral_filter_of_dominated_convergence (fun y => ‖f y‖) ?_ ?_ hf.norm ?_` and prove the remaining obligations. Use `Eventually.of_forall fun ε => ?_` and prove the remaining obligations. Use `Continuous.aestronglyMeasurable ?_ |>.mul hf.aestronglyMeasurable` and prove the remaining obligations. Use `fun_prop`.

Use `filter_upwards [self_mem_nhdsWithin] with ε hε`. Use `Eventually.of_forall fun y => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (norm_exp_reg_le hε y)`. Use `Eventually.of_forall fun y => ?_` and prove the remaining obligations.

Establish `hc : Continuous fun ε : ℝ => Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) * f y` using `by fun_prop`. Use `(hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))` as an intermediate fact. Simplify using `using this`.
-/
theorem tendsto_reg_left {f : ℂ → ℂ} (hf : Integrable f volC) :
    Tendsto (fun ε : ℝ => ∫ y, Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) * f y ∂volC) (𝓝[>] 0) (𝓝 (∫ y, f y ∂volC)) := by
  have hs := Complex.continuous_normSq
  refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖f y‖) ?_ ?_ hf.norm ?_
  · refine Eventually.of_forall fun ε => ?_
    refine Continuous.aestronglyMeasurable ?_ |>.mul hf.aestronglyMeasurable
    fun_prop
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine Eventually.of_forall fun y => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_exp_reg_le hε y)
  · refine Eventually.of_forall fun y => ?_
    have hc : Continuous fun ε : ℝ => Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) * f y := by
      fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this

/- English proof (translation)
Use `set b : ℂ := (ε : ℂ) - 2 * Real.pi * t * Complex.I with hbd`. Establish `hre : b.re = ε` using `by simp [hbd]`. Establish `him : b.im = -(2 * Real.pi * t)` using `by simp [hbd]`. Establish `hb0 : b ≠ 0`. Introduce `h`.

Rewrite `hre` using `[h]`. Simplify using `at hre`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpi` using `Real.pi_pos`. Establish `ht' : 0 < |t|` using `abs_pos.2 ht`.

Establish `hnb : 2 * Real.pi * |t| ≤ ‖b‖`. Establish `h1` using `Complex.abs_im_le_norm b`. Rewrite `h1` using `[him, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]`. Conclude with `h1`. Establish `h1 : ‖2 * (Real.pi : ℂ) / b‖ ≤ |t|⁻¹`.

Rewrite using `[norm_div]`. Establish `: ‖2 * (Real.pi : ℂ)‖ = 2 * Real.pi`. Simplify using `[abs_of_pos hpi]`. Rewrite using `[this, div_le_iff₀ (norm_pos_iff.2 hb0)]`. Establish `: |t|⁻¹ * (2 * Real.pi * |t|) ≤ |t|⁻¹ * ‖b‖` using `mul_le_mul_of_nonneg_left hnb (by positivity)`.

Establish `e : |t|⁻¹ * (2 * Real.pi * |t|) = 2 * Real.pi`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : ‖Complex.exp (-(4 * Real.pi ^ 2 * (Complex.normSq w : ℂ)) / b)‖ ≤ 1`. Rewrite using `[Complex.norm_exp]`.

Use `Real.exp_le_one_iff.2 ?_` and prove the remaining obligations. Establish `e : -(4 * (Real.pi : ℂ) ^ 2 * (Complex.normSq w : ℂ)) / b = ((-(4 * Real.pi ^ 2 * Complex.normSq w) : ℝ) : ℂ) / b`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Complex.div_re]`.

Simplify using `only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero, hre]`. Establish `hN` using `Complex.normSq_nonneg w`. Establish `: 0 ≤ (4 * Real.pi ^ 2 * Complex.normSq w) * ε / Complex.normSq b` using `div_nonneg (by positivity) (Complex.normSq_nonneg _)`. Establish `e2 : -(4 * Real.pi ^ 2 * Complex.normSq w) * ε / Complex.normSq b = -((4 * Real.pi ^ 2 * Complex.normSq w) * ε / Complex.normSq b)` using `by ring`. Rewrite using `[e2]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Gs, ← hbd, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_Gs_le {ε t : ℝ} (hε : 0 < ε) (ht : t ≠ 0) (w : ℂ) : ‖Gs ε t w‖ ≤ |t|⁻¹ := by
  set b : ℂ := (ε : ℂ) - 2 * Real.pi * t * Complex.I with hbd
  have hre : b.re = ε := by simp [hbd]
  have him : b.im = -(2 * Real.pi * t) := by simp [hbd]
  have hb0 : b ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  have hpi := Real.pi_pos
  have ht' : 0 < |t| := abs_pos.2 ht
  have hnb : 2 * Real.pi * |t| ≤ ‖b‖ := by
    have h1 := Complex.abs_im_le_norm b
    rw [him, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at h1
    exact h1
  have h1 : ‖2 * (Real.pi : ℂ) / b‖ ≤ |t|⁻¹ := by
    rw [norm_div]
    have : ‖2 * (Real.pi : ℂ)‖ = 2 * Real.pi := by
      simp [abs_of_pos hpi]
    rw [this, div_le_iff₀ (norm_pos_iff.2 hb0)]
    have : |t|⁻¹ * (2 * Real.pi * |t|) ≤ |t|⁻¹ * ‖b‖ := mul_le_mul_of_nonneg_left hnb (by positivity)
    have e : |t|⁻¹ * (2 * Real.pi * |t|) = 2 * Real.pi := by
      field_simp
    linarith
  have h2 : ‖Complex.exp (-(4 * Real.pi ^ 2 * (Complex.normSq w : ℂ)) / b)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    refine Real.exp_le_one_iff.2 ?_
    have e : -(4 * (Real.pi : ℂ) ^ 2 * (Complex.normSq w : ℂ)) / b = ((-(4 * Real.pi ^ 2 * Complex.normSq w) : ℝ) : ℂ) / b := by
      push_cast
      ring
    rw [e, Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero, hre]
    have hN := Complex.normSq_nonneg w
    have : 0 ≤ (4 * Real.pi ^ 2 * Complex.normSq w) * ε / Complex.normSq b :=
      div_nonneg (by positivity) (Complex.normSq_nonneg _)
    have e2 : -(4 * Real.pi ^ 2 * Complex.normSq w) * ε / Complex.normSq b = -((4 * Real.pi ^ 2 * Complex.normSq w) * ε / Complex.normSq b) := by ring
    rw [e2]
    linarith
  rw [Gs, ← hbd, norm_mul]
  calc _ ≤ |t|⁻¹ * 1 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

/- English proof (translation)
Establish `htc : (t : ℂ) ≠ 0` using `by exact_mod_cast ht`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `hb0 : ((0 : ℝ) : ℂ) - 2 * Real.pi * t * Complex.I ≠ 0`. Simplify using `[Real.pi_ne_zero, ht]`. Establish `hbc : Continuous fun ε : ℝ => (ε : ℂ) - 2 * Real.pi * t * Complex.I` using `by fun_prop`.

Establish `hb` using `hbc.tendsto 0`. Establish `h1 : Tendsto (fun ε : ℝ => Gs ε t w) (𝓝 0) (𝓝 (Gs 0 t w))`. Unfold `Gs`. Conclude with `(tendsto_const_nhds.div hb hb0).mul ((tendsto_const_nhds.div hb hb0).cexp)`. Establish `hv : Gs 0 t w = (Complex.I / (t : ℂ)) * ee (-(Complex.normSq w) / t)`.

Unfold `Gs ee`. Use `congr 1`. Rewrite using `[Complex.ofReal_zero, zero_sub, div_eq_div_iff (by simp [Real.pi_ne_zero, ht]) htc]`. Put the polynomial expressions in normal form. Simplify using `only [Complex.I_sq]`.

Expand and normalize the polynomial expressions, which then agree. Use `congr 1`. Rewrite using `[Complex.ofReal_zero, zero_sub, div_eq_iff (by simp [Real.pi_ne_zero, ht])]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Put the polynomial expressions in normal form. Simplify using `only [Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hv]`. Conclude with `h1.mono_left nhdsWithin_le_nhds`.
-/
theorem tendsto_Gs {t : ℝ} (ht : t ≠ 0) (w : ℂ) :
    Tendsto (fun ε : ℝ => Gs ε t w) (𝓝[>] 0) (𝓝 ((Complex.I / (t : ℂ)) * ee (-(Complex.normSq w) / t))) := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hb0 : ((0 : ℝ) : ℂ) - 2 * Real.pi * t * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, ht]
  have hbc : Continuous fun ε : ℝ => (ε : ℂ) - 2 * Real.pi * t * Complex.I := by fun_prop
  have hb := hbc.tendsto 0
  have h1 : Tendsto (fun ε : ℝ => Gs ε t w) (𝓝 0) (𝓝 (Gs 0 t w)) := by
    unfold Gs
    exact (tendsto_const_nhds.div hb hb0).mul ((tendsto_const_nhds.div hb hb0).cexp)
  have hv : Gs 0 t w = (Complex.I / (t : ℂ)) * ee (-(Complex.normSq w) / t) := by
    unfold Gs ee
    congr 1
    · rw [Complex.ofReal_zero, zero_sub, div_eq_div_iff (by simp [Real.pi_ne_zero, ht]) htc]
      ring_nf
      simp only [Complex.I_sq]
      ring
    · congr 1
      rw [Complex.ofReal_zero, zero_sub, div_eq_iff (by simp [Real.pi_ne_zero, ht])]
      push_cast
      field_simp
      ring_nf
      simp only [Complex.I_sq]
      ring
  rw [← hv]
  exact h1.mono_left nhdsWithin_le_nhds

/- English proof (translation)
Rewrite using `[← integral_const_mul]`. Establish `hcont : ∀ ε : ℝ, 0 < ε → Continuous fun u => Gs ε t (z + u)`. Introduce `ε hε`. Establish `hs` using `Complex.continuous_normSq`. Unfold `Gs`.

Use `fun_prop`. Use `tendsto_integral_filter_of_dominated_convergence (fun u => |t|⁻¹ * ‖Ψ u‖) ?_ ?_ (hΨ.norm.const_mul _) ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with ε hε`. Conclude with `(hcont ε hε).aestronglyMeasurable.mul hΨ.aestronglyMeasurable`. Use `filter_upwards [self_mem_nhdsWithin] with ε hε`.

Use `Eventually.of_forall fun u => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (norm_Gs_le hε ht _) (norm_nonneg _)`. Use `Eventually.of_forall fun u => ?_` and prove the remaining obligations. Use `(tendsto_Gs ht (z + u)).mul_const (Ψ u)` as an intermediate fact.

Simplify `this` using `[mul_assoc]`.
-/
theorem tendsto_reg_right {t : ℝ} (ht : t ≠ 0) {Ψ : ℂ → ℂ} (hΨ : Integrable Ψ volC) (z : ℂ) :
    Tendsto (fun ε : ℝ => ∫ u, Gs ε t (z + u) * Ψ u ∂volC) (𝓝[>] 0)
      (𝓝 ((Complex.I / (t : ℂ)) * ∫ u, ee (-(Complex.normSq (z + u)) / t) * Ψ u ∂volC)) := by
  rw [← integral_const_mul]
  have hcont : ∀ ε : ℝ, 0 < ε → Continuous fun u => Gs ε t (z + u) := by
    intro ε hε
    have hs := Complex.continuous_normSq
    unfold Gs
    fun_prop
  refine tendsto_integral_filter_of_dominated_convergence (fun u => |t|⁻¹ * ‖Ψ u‖) ?_ ?_ (hΨ.norm.const_mul _) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hcont ε hε).aestronglyMeasurable.mul hΨ.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine Eventually.of_forall fun u => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_Gs_le hε ht _) (norm_nonneg _)
  · refine Eventually.of_forall fun u => ?_
    have := (tendsto_Gs ht (z + u)).mul_const (Ψ u)
    simpa [mul_assoc] using this

/- English proof (translation)
Take `⟨f, rfl⟩` from `hΦ`. Establish `h : Integrable (⇑f) (volume : Measure ℂ)` using `f.integrable`. Conclude with `h.smul_measure (by simp)`.
-/
theorem sch_integrable {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) : Integrable Φ volC := by
  obtain ⟨f, rfl⟩ := hΦ
  have h : Integrable (⇑f) (volume : Measure ℂ) := f.integrable
  exact h.smul_measure (by simp)

/- English proof (translation)
Establish `hFi` using `sch_integrable (Fr_mem hΨ)`. Establish `hf : Integrable (fun y => ee (t * Complex.normSq y + 2 * (conj z * y).re) * Fr Ψ y) volC`. Use `hFi.bdd_mul (c := 1) ?_ ?_` and prove the remaining obligations. Conclude with `(continuous_ee.comp (by fun_prop)).aestronglyMeasurable`. Conclude with `Eventually.of_forall fun y => (norm_ee _).le`.

Establish `hL` using `tendsto_reg_left hf`. Establish `hR` using `tendsto_reg_right ht (sch_integrable hΨ) z`. Use `tendsto_nhds_unique (hL.congr' ?_) hR` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with ε hε`. Establish `hε' : (0 : ℝ) < ε` using `hε`.

Establish `hKc : Continuous fun y : ℂ => Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) * ee (t * Complex.normSq y)`. Use `continuous_ee` as an intermediate fact. Use `Complex.continuous_normSq` as an intermediate fact. Use `fun_prop`. Establish `hKi : Integrable (fun y : ℂ => Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) * ee (t * Complex.normSq y)) volC`.

Establish `hb : 0 < ((ε : ℂ) - 2 * Real.pi * t * Complex.I).re` using `by simpa using hε'`. Establish `h0` using `GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 0`. Establish `h1 : Integrable (fun y : ℂ => Complex.exp (-((ε : ℂ) - 2 * Real.pi * t * Complex.I) * (‖y‖ : ℂ) ^ 2)) (volume : Measure ℂ)`. Simplify using `using h0`. Establish `h2` using `h1.smul_measure (c := (2 : ENNReal)) (by simp)`.

Use `h2.congr (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [ee, ← Complex.exp_add]`. Use `congr 1`. Rewrite using `[Complex.normSq_eq_norm_sq]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `h` using `fubini_Fr hKi hKc hΨ z`. Combine the equalities or inequalities in the displayed calculation. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [ee_add]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := h`. Use `_ = _ := by`. Use `integral_congr_ae (Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Simplify using `only []`.

Rewrite using `[← gauss_int ε t hε']`. Use `congr 1`. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [ee_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gauss {t : ℝ} (ht : t ≠ 0) {Ψ : ℂ → ℂ} (hΨ : Ψ ∈ SchC) (z : ℂ) :
    ∫ y, ee (t * Complex.normSq y + 2 * (conj z * y).re) * Fr Ψ y ∂volC =
      (Complex.I / (t : ℂ)) * ∫ u, ee (-(Complex.normSq (z + u)) / t) * Ψ u ∂volC := by
  have hFi := sch_integrable (Fr_mem hΨ)
  have hf : Integrable (fun y => ee (t * Complex.normSq y + 2 * (conj z * y).re) * Fr Ψ y) volC := by
    refine hFi.bdd_mul (c := 1) ?_ ?_
    · exact (continuous_ee.comp (by fun_prop)).aestronglyMeasurable
    · exact Eventually.of_forall fun y => (norm_ee _).le
  have hL := tendsto_reg_left hf
  have hR := tendsto_reg_right ht (sch_integrable hΨ) z
  refine tendsto_nhds_unique (hL.congr' ?_) hR
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have hKc : Continuous fun y : ℂ => Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) * ee (t * Complex.normSq y) := by
    have := continuous_ee
    have := Complex.continuous_normSq
    fun_prop
  have hKi : Integrable (fun y : ℂ => Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) * ee (t * Complex.normSq y)) volC := by
    have hb : 0 < ((ε : ℂ) - 2 * Real.pi * t * Complex.I).re := by simpa using hε'
    have h0 := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 0
    have h1 : Integrable (fun y : ℂ => Complex.exp (-((ε : ℂ) - 2 * Real.pi * t * Complex.I) * (‖y‖ : ℂ) ^ 2)) (volume : Measure ℂ) := by
      simpa using h0
    have h2 := h1.smul_measure (c := (2 : ENNReal)) (by simp)
    refine h2.congr (Eventually.of_forall fun y => ?_)
    simp only [ee, ← Complex.exp_add]
    congr 1
    rw [Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have h := fubini_Fr hKi hKc hΨ z
  calc _ = ∫ y, Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) * ee (t * Complex.normSq y) * ee (2 * (conj z * y).re) * Fr Ψ y ∂volC := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [ee_add]
        ring
    _ = _ := h
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only []
        rw [← gauss_int ε t hε']
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [ee_add]
        ring

/- English proof (translation)
Rewrite using `[rWR_zero, mul_assoc (ee _), sgR_mul_abs ha]`.
-/
theorem rWR_zero' {a : ℝ} (ha : a ≠ 0) (b d : ℝ) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR a b 0 d Φ z = ee (a * b * Complex.normSq z) * (a : ℂ) * Φ ((a : ℂ) * z) := by
  rw [rWR_zero, mul_assoc (ee _), sgR_mul_abs ha]

/- English proof (translation)
Establish `h` using `sgR_mul_abs_inv (neg_ne_zero.2 hc)`. Rewrite `h` using `[abs_neg, inv_neg]`. Rewrite using `[rWR_ne a b d hc, mul_assoc Complex.I, h]`.
-/
theorem rWR_ne' (a b d : ℝ) {c : ℝ} (hc : c ≠ 0) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR a b c d Φ z = Complex.I * ((-c⁻¹ : ℝ) : ℂ) *
      ∫ u, ee ((a * Complex.normSq z + d * Complex.normSq u - 2 * (conj z * u).re) / c) * Φ u ∂volC := by
  have h := sgR_mul_abs_inv (neg_ne_zero.2 hc)
  rw [abs_neg, inv_neg] at h
  rw [rWR_ne a b d hc, mul_assoc Complex.I, h]

/- English proof (translation)
Establish `h` using `sgR_mul_abs_inv (neg_ne_zero.2 hc)`. Rewrite `h` using `[abs_neg, inv_neg]`. Rewrite using `[rWR_fr a b d hc, mul_assoc Complex.I, h]`.
-/
theorem rWR_fr' (a b d : ℝ) {c : ℝ} (hc : c ≠ 0) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR a b c d Φ z = Complex.I * ((-c⁻¹ : ℝ) : ℂ) * (ee (a / c * Complex.normSq z) *
      Fr (fun u => ee (d / c * Complex.normSq u) * Φ u) (((-c⁻¹ : ℝ) : ℂ) * z)) := by
  have h := sgR_mul_abs_inv (neg_ne_zero.2 hc)
  rw [abs_neg, inv_neg] at h
  rw [rWR_fr a b d hc, mul_assoc Complex.I, h]

/- English proof (translation)
Rewrite using `[rWR_zero' one_ne_zero]`. Simplify using the standard rewrite rules.
-/
theorem rWR_n (x : ℝ) (F : ℂ → ℂ) (z : ℂ) : rWR 1 x 0 1 F z = ee (x * Complex.normSq z) * F z := by
  rw [rWR_zero' one_ne_zero]
  simp

/- English proof (translation)
Rewrite using `[rWR_zero' hs]`. Simplify using the standard rewrite rules.
-/
theorem rWR_m {s : ℝ} (hs : s ≠ 0) (F : ℂ → ℂ) (z : ℂ) : rWR s 0 0 s⁻¹ F z = (s : ℂ) * F ((s : ℂ) * z) := by
  rw [rWR_zero' hs]
  simp

/- English proof (translation)
Rewrite using `[rWR_n]`. Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Establish `had : a * d = 1` using `by simpa using h`. Rewrite using `[rWR_zero, rWR_zero]`.

Establish `e : (a + x * 0) * (b + x * d) * Complex.normSq z = x * Complex.normSq z + a * b * Complex.normSq z`. Take the linear combination `(x * Complex.normSq z) * had`. Rewrite using `[e, ee_add]`. Simplify using `only [mul_zero, add_zero]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[rWR_ne' _ _ _ hc, rWR_ne' _ _ _ hc, mul_left_comm, ← integral_const_mul (μ := volC) (ee (x * Complex.normSq z))]`. Use `congr 1`. Use `integral_congr_ae (Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Use `show ee _ * Φ u = ee _ * (ee _ * Φ u)`. Rewrite using `[← mul_assoc, ← ee_add]`.

Use `congr 2`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Pn (x a b c d : ℝ) (h : a * d - b * c = 1) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR (a + x * c) (b + x * d) c d Φ z = rWR 1 x 0 1 (rWR a b c d Φ) z := by
  rw [rWR_n]
  by_cases hc : c = 0
  · subst hc
    have had : a * d = 1 := by simpa using h
    rw [rWR_zero, rWR_zero]
    have e : (a + x * 0) * (b + x * d) * Complex.normSq z = x * Complex.normSq z + a * b * Complex.normSq z := by
      linear_combination (x * Complex.normSq z) * had
    rw [e, ee_add]
    simp only [mul_zero, add_zero]
    ring
  · rw [rWR_ne' _ _ _ hc, rWR_ne' _ _ _ hc, mul_left_comm, ← integral_const_mul (μ := volC) (ee (x * Complex.normSq z))]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show ee _ * Φ u = ee _ * (ee _ * Φ u)
    rw [← mul_assoc, ← ee_add]
    congr 2
    field_simp
    ring

/- English proof (translation)
Rewrite using `[rWR_m hs]`. Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Establish `had : a * d = 1` using `by simpa using h`. Establish `ha : a ≠ 0` using `left_ne_zero_of_mul_eq_one had`.

Rewrite using `[zero_div, rWR_zero' (mul_ne_zero hs ha), rWR_zero' ha, Complex.normSq_mul, Complex.normSq_ofReal]`. Establish `e : s * a * (s * b) * Complex.normSq z = a * b * (s * s * Complex.normSq z)` using `by ring`. Rewrite using `[e]`. Use `push_cast`. Put the polynomial expressions in normal form.

Establish `hcs : c / s ≠ 0` using `div_ne_zero hc hs`. Rewrite using `[rWR_ne' _ _ _ hcs, rWR_ne' _ _ _ hc]`. Establish `hI : ∫ u, ee ((s * a * Complex.normSq z + d / s * Complex.normSq u - 2 * (conj z * u).re) / (c / s)) * Φ u ∂volC = ∫ u, ee ((a * Complex.normSq ((s : ℂ) * z) + d * Complex.normSq u - 2 * (conj ((s : ℂ) * z) * u).re) / c) * Φ u ∂volC`. Use `integral_congr_ae (Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Use `show ee _ * Φ u = ee _ * Φ u`.

Establish `e2 : (conj ((s : ℂ) * z) * u).re = s * (conj z * u).re`. Rewrite using `[map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]`. Rewrite using `[e2, Complex.normSq_mul, Complex.normSq_ofReal]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hI]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem Pm {s : ℝ} (hs : s ≠ 0) (a b c d : ℝ) (h : a * d - b * c = 1) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR (s * a) (s * b) (c / s) (d / s) Φ z = rWR s 0 0 s⁻¹ (rWR a b c d Φ) z := by
  rw [rWR_m hs]
  by_cases hc : c = 0
  · subst hc
    have had : a * d = 1 := by simpa using h
    have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one had
    rw [zero_div, rWR_zero' (mul_ne_zero hs ha), rWR_zero' ha, Complex.normSq_mul, Complex.normSq_ofReal]
    have e : s * a * (s * b) * Complex.normSq z = a * b * (s * s * Complex.normSq z) := by ring
    rw [e]
    push_cast
    ring_nf
  · have hcs : c / s ≠ 0 := div_ne_zero hc hs
    rw [rWR_ne' _ _ _ hcs, rWR_ne' _ _ _ hc]
    have hI : ∫ u, ee ((s * a * Complex.normSq z + d / s * Complex.normSq u - 2 * (conj z * u).re) / (c / s)) * Φ u ∂volC =
        ∫ u, ee ((a * Complex.normSq ((s : ℂ) * z) + d * Complex.normSq u - 2 * (conj ((s : ℂ) * z) * u).re) / c) * Φ u ∂volC := by
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      show ee _ * Φ u = ee _ * Φ u
      have e2 : (conj ((s : ℂ) * z) * u).re = s * (conj z * u).re := by
        rw [map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
      rw [e2, Complex.normSq_mul, Complex.normSq_ofReal]
      congr 2
      field_simp
    rw [hI]
    push_cast
    field_simp

/- English proof (translation)
Rewrite using `[rWR_ne' 0 1 0 (by norm_num : (-1 : ℝ) ≠ 0)]`. Use `set H : ℂ → ℂ := fun u => ee ((0 * Complex.normSq z + 0 * Complex.normSq u - 2 * (conj z * u).re) / (-1)) * rWR a b c d Φ u with hH`. Establish `hs : (-c : ℝ) ≠ 0` using `neg_ne_zero.2 hc`. Establish `h` using `integral_volC_smul H hs`. Establish `h2 : ∫ u, H u ∂volC = ((c ^ 2 : ℝ) : ℂ) * ∫ u, H (((-c : ℝ) : ℂ) * u) ∂volC`.

Rewrite using `[h, neg_sq, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (pow_ne_zero 2 hc)]`. Simplify using the standard rewrite rules. Use `show Complex.I * (((-(-1 : ℝ)⁻¹ : ℝ)) : ℂ) * ∫ u, H u ∂volC = _`. Rewrite using `[h2]`. Establish `h3 : ∀ v : ℂ, H (((-c : ℝ) : ℂ) * v) = (Complex.I * ((-c⁻¹ : ℝ) : ℂ)) * (ee (a * c * Complex.normSq v + 2 * (conj (((-c : ℝ) : ℂ) * z) * v).re) * Fr (fun u => ee (d / c * Complex.normSq u) * Φ u) v)`.

Introduce `v`. Simplify using `only [hH]`. Rewrite using `[rWR_fr' a b d hc]`. Establish `e1 : (((-c⁻¹ : ℝ) : ℂ) * (((-c : ℝ) : ℂ) * v)) = v`. Establish `hc' : (c : ℂ) ≠ 0` using `by exact_mod_cast hc`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `e2 : (conj (((-c : ℝ) : ℂ) * z) * v).re = -c * (conj z * v).re`. Rewrite using `[map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]`. Establish `e3 : (conj z * (((-c : ℝ) : ℂ) * v)).re = -c * (conj z * v).re`.

Rewrite using `[mul_left_comm, Complex.re_ofReal_mul]`. Rewrite using `[e1, ee_add, e2, e3, Complex.normSq_mul, Complex.normSq_ofReal]`. Establish `e4 : (0 * Complex.normSq z + 0 * (Complex.normSq ((-c : ℝ) : ℂ) * Complex.normSq v) - 2 * (-c * (conj z * v).re)) / (-1) = 2 * (-c * (conj z * v).re)` using `by ring`. Establish `e5 : (0 * Complex.normSq z + 0 * (-c * -c * Complex.normSq v) - 2 * (-c * (conj z * v).re)) / (-1) = 2 * (-c * (conj z * v).re)` using `by ring`. Establish `e6 : a / c * (-c * -c * Complex.normSq v) = a * c * Complex.normSq v`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e5, e6]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h3]`. Rewrite using `[integral_const_mul]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Pw_common (a b d : ℝ) {c : ℝ} (hc : c ≠ 0) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR 0 1 (-1) 0 (rWR a b c d Φ) z = (c : ℂ) * ∫ v, ee (a * c * Complex.normSq v + 2 * (conj (((-c : ℝ) : ℂ) * z) * v).re) *
      Fr (fun u => ee (d / c * Complex.normSq u) * Φ u) v ∂volC := by
  rw [rWR_ne' 0 1 0 (by norm_num : (-1 : ℝ) ≠ 0)]
  set H : ℂ → ℂ := fun u => ee ((0 * Complex.normSq z + 0 * Complex.normSq u - 2 * (conj z * u).re) / (-1)) * rWR a b c d Φ u with hH
  have hs : (-c : ℝ) ≠ 0 := neg_ne_zero.2 hc
  have h := integral_volC_smul H hs
  have h2 : ∫ u, H u ∂volC = ((c ^ 2 : ℝ) : ℂ) * ∫ u, H (((-c : ℝ) : ℂ) * u) ∂volC := by
    rw [h, neg_sq, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (pow_ne_zero 2 hc)]
    simp
  show Complex.I * (((-(-1 : ℝ)⁻¹ : ℝ)) : ℂ) * ∫ u, H u ∂volC = _
  rw [h2]
  have h3 : ∀ v : ℂ, H (((-c : ℝ) : ℂ) * v) = (Complex.I * ((-c⁻¹ : ℝ) : ℂ)) * (ee (a * c * Complex.normSq v + 2 * (conj (((-c : ℝ) : ℂ) * z) * v).re) *
      Fr (fun u => ee (d / c * Complex.normSq u) * Φ u) v) := by
    intro v
    simp only [hH]
    rw [rWR_fr' a b d hc]
    have e1 : (((-c⁻¹ : ℝ) : ℂ) * (((-c : ℝ) : ℂ) * v)) = v := by
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
      push_cast
      field_simp
    have e2 : (conj (((-c : ℝ) : ℂ) * z) * v).re = -c * (conj z * v).re := by
      rw [map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
    have e3 : (conj z * (((-c : ℝ) : ℂ) * v)).re = -c * (conj z * v).re := by
      rw [mul_left_comm, Complex.re_ofReal_mul]
    rw [e1, ee_add, e2, e3, Complex.normSq_mul, Complex.normSq_ofReal]
    have e4 : (0 * Complex.normSq z + 0 * (Complex.normSq ((-c : ℝ) : ℂ) * Complex.normSq v) - 2 * (-c * (conj z * v).re)) / (-1) = 2 * (-c * (conj z * v).re) := by ring
    have e5 : (0 * Complex.normSq z + 0 * (-c * -c * Complex.normSq v) - 2 * (-c * (conj z * v).re)) / (-1) = 2 * (-c * (conj z * v).re) := by ring
    have e6 : a / c * (-c * -c * Complex.normSq v) = a * c * Complex.normSq v := by
      field_simp
    rw [e5, e6]
    ring
  simp only [h3]
  rw [integral_const_mul]
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring

/- English proof (translation)
Establish `ha : a ≠ 0` using `left_ne_zero_of_mul_eq_one had`. Establish `ha' : -a ≠ 0` using `neg_ne_zero.2 ha`. Establish `hac : (a : ℂ) ≠ 0` using `by exact_mod_cast ha`. Rewrite using `[rWR_ne' _ _ _ ha', rWR_ne' 0 1 0 (by norm_num : (-1 : ℝ) ≠ 0)]`. Use `set f : ℂ → ℂ := fun u => ee ((0 * Complex.normSq z + -b * Complex.normSq u - 2 * (conj z * u).re) / (-a)) * Φ u with hf`.

Establish `h` using `integral_volC_smul f ha`. Establish `h1 : ∫ u, ee ((0 * Complex.normSq z + 0 * Complex.normSq u - 2 * (conj z * u).re) / (-1)) * rWR a b 0 d Φ u ∂volC = (a : ℂ) * ∫ u, f ((a : ℂ) * u) ∂volC`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Use `show _ * _ = (a : ℂ) * (ee _ * Φ _)`.

Rewrite using `[rWR_zero' ha]`. Establish `e2 : (conj z * ((a : ℂ) * u)).re = a * (conj z * u).re`. Rewrite using `[mul_left_comm, Complex.re_ofReal_mul]`. Establish `e : (0 * Complex.normSq z + -b * Complex.normSq ((a : ℂ) * u) - 2 * (conj z * ((a : ℂ) * u)).re) / (-a) = (0 * Complex.normSq z + 0 * Complex.normSq u - 2 * (conj z * u).re) / (-1) + a * b * Complex.normSq u`. Rewrite using `[e2, Complex.normSq_mul, Complex.normSq_ofReal]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ee_add]`. Expand and normalize the polynomial expressions, which then agree. Use `show Complex.I * _ * ∫ u, f u ∂volC = _`.

Rewrite using `[h1, h]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem Pw0 {a b d : ℝ} (had : a * d = 1) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR 0 d (-a) (-b) Φ z = rWR 0 1 (-1) 0 (rWR a b 0 d Φ) z := by
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one had
  have ha' : -a ≠ 0 := neg_ne_zero.2 ha
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  rw [rWR_ne' _ _ _ ha', rWR_ne' 0 1 0 (by norm_num : (-1 : ℝ) ≠ 0)]
  set f : ℂ → ℂ := fun u => ee ((0 * Complex.normSq z + -b * Complex.normSq u - 2 * (conj z * u).re) / (-a)) * Φ u with hf
  have h := integral_volC_smul f ha
  have h1 : ∫ u, ee ((0 * Complex.normSq z + 0 * Complex.normSq u - 2 * (conj z * u).re) / (-1)) * rWR a b 0 d Φ u ∂volC =
      (a : ℂ) * ∫ u, f ((a : ℂ) * u) ∂volC := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show _ * _ = (a : ℂ) * (ee _ * Φ _)
    rw [rWR_zero' ha]
    have e2 : (conj z * ((a : ℂ) * u)).re = a * (conj z * u).re := by
      rw [mul_left_comm, Complex.re_ofReal_mul]
    have e : (0 * Complex.normSq z + -b * Complex.normSq ((a : ℂ) * u) - 2 * (conj z * ((a : ℂ) * u)).re) / (-a) =
        (0 * Complex.normSq z + 0 * Complex.normSq u - 2 * (conj z * u).re) / (-1) + a * b * Complex.normSq u := by
      rw [e2, Complex.normSq_mul, Complex.normSq_ofReal]
      field_simp
      ring
    rw [e, ee_add]
    ring
  show Complex.I * _ * ∫ u, f u ∂volC = _
  rw [h1, h]
  push_cast
  field_simp

/- English proof (translation)
Establish `hc : c ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hbc`. Establish `hΨ` using `chirp_mem (d / c) hΦ`. Rewrite using `[Pw_common 0 b d hc, rWR_zero' hc]`.

Establish `h1 : ∫ v, ee (0 * c * Complex.normSq v + 2 * (conj (((-c : ℝ) : ℂ) * z) * v).re) * Fr (fun u => ee (d / c * Complex.normSq u) * Φ u) v ∂volC = Fr (Fr (fun u => ee (d / c * Complex.normSq u) * Φ u)) (((-c : ℝ) : ℂ) * z)`. Rewrite using `[Fr]`. Use `integral_congr_ae (Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[h1, Fr_Fr hΨ]`.

Establish `e : -(((-c : ℝ) : ℂ) * z) = (c : ℂ) * z`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Complex.normSq_mul, Complex.normSq_ofReal]`. Establish `e2 : d / c * (c * c * Complex.normSq z) = c * d * Complex.normSq z`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Pw1 {b c d : ℝ} (hbc : b * c = -1) {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) (z : ℂ) :
    rWR c d 0 (-b) Φ z = rWR 0 1 (-1) 0 (rWR 0 b c d Φ) z := by
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hbc
  have hΨ := chirp_mem (d / c) hΦ
  rw [Pw_common 0 b d hc, rWR_zero' hc]
  have h1 : ∫ v, ee (0 * c * Complex.normSq v + 2 * (conj (((-c : ℝ) : ℂ) * z) * v).re) *
      Fr (fun u => ee (d / c * Complex.normSq u) * Φ u) v ∂volC = Fr (Fr (fun u => ee (d / c * Complex.normSq u) * Φ u)) (((-c : ℝ) : ℂ) * z) := by
    rw [Fr]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp
  rw [h1, Fr_Fr hΨ]
  have e : -(((-c : ℝ) : ℂ) * z) = (c : ℂ) * z := by
    push_cast
    ring
  rw [e, Complex.normSq_mul, Complex.normSq_ofReal]
  have e2 : d / c * (c * c * Complex.normSq z) = c * d * Complex.normSq z := by
    field_simp
  rw [e2]
  ring

/- English proof (translation)
Establish `hΨ` using `chirp_mem (d / c) hΦ`. Establish `ha' : -a ≠ 0` using `neg_ne_zero.2 ha`. Establish `hac : (a : ℂ) ≠ 0` using `by exact_mod_cast ha`. Establish `hcc : (c : ℂ) ≠ 0` using `by exact_mod_cast hc`. Rewrite using `[Pw_common a b d hc, gauss (mul_ne_zero ha hc) hΨ, rWR_ne' _ _ _ ha']`.

Establish `h1 : ∫ u, ee (-(Complex.normSq (((-c : ℝ) : ℂ) * z + u)) / (a * c)) * (ee (d / c * Complex.normSq u) * Φ u) ∂volC = ∫ u, ee ((c * Complex.normSq z + -b * Complex.normSq u - 2 * (conj z * u).re) / (-a)) * Φ u ∂volC`. Use `integral_congr_ae (Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Use `show _ * _ = _ * _`. Rewrite using `[← mul_assoc, ← ee_add]`. Use `congr 2`.

Establish `e1 : Complex.normSq (((-c : ℝ) : ℂ) * z + u) = c ^ 2 * Complex.normSq z + Complex.normSq u - 2 * c * (conj z * u).re`. Rewrite using `[Complex.normSq_add, Complex.normSq_mul, Complex.normSq_ofReal]`. Simplify using `only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`.

Establish `hb : b = (a * d - 1) / c`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hb]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem Pw2 {a b c d : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) (h : a * d - b * c = 1) {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) (z : ℂ) :
    rWR c d (-a) (-b) Φ z = rWR 0 1 (-1) 0 (rWR a b c d Φ) z := by
  have hΨ := chirp_mem (d / c) hΦ
  have ha' : -a ≠ 0 := neg_ne_zero.2 ha
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [Pw_common a b d hc, gauss (mul_ne_zero ha hc) hΨ, rWR_ne' _ _ _ ha']
  have h1 : ∫ u, ee (-(Complex.normSq (((-c : ℝ) : ℂ) * z + u)) / (a * c)) * (ee (d / c * Complex.normSq u) * Φ u) ∂volC =
      ∫ u, ee ((c * Complex.normSq z + -b * Complex.normSq u - 2 * (conj z * u).re) / (-a)) * Φ u ∂volC := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show _ * _ = _ * _
    rw [← mul_assoc, ← ee_add]
    congr 2
    have e1 : Complex.normSq (((-c : ℝ) : ℂ) * z + u) = c ^ 2 * Complex.normSq z + Complex.normSq u - 2 * c * (conj z * u).re := by
      rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_ofReal]
      simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [e1]
    have hb : b = (a * d - 1) / c := by
      field_simp
      linarith
    rw [hb]
    field_simp
    ring
  rw [h1]
  push_cast
  field_simp

/- English proof (translation)
Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Establish `had : a * d = 1` using `by simpa using h`. Establish `ha : a ≠ 0` using `left_ne_zero_of_mul_eq_one had`. Establish `e : rWR a b 0 d Φ = fun z => (a : ℂ) * (ee (a * b * Complex.normSq z) * Φ ((a : ℂ) * z))`.

Use function extensionality and compare the values at `z`. Rewrite using `[rWR_zero' ha]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `const_mem _ (chirp_mem _ (dil_mem ha hΦ))`.

Establish `e : rWR a b c d Φ = fun z => (Complex.I * ((-c⁻¹ : ℝ) : ℂ)) * (ee (a / c * Complex.normSq z) * Fr (fun u => ee (d / c * Complex.normSq u) * Φ u) (((-c⁻¹ : ℝ) : ℂ) * z))`. Use function extensionality and compare the values at `fun z => rWR_fr' a b d hc Φ z`. Rewrite using `[e]`. Conclude with `const_mem _ (chirp_mem _ (dil_mem (neg_ne_zero.2 (inv_ne_zero hc)) (Fr_mem (chirp_mem _ hΦ))))`.
-/
theorem rWR_mem {a b c d : ℝ} (h : a * d - b * c = 1) {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) : rWR a b c d Φ ∈ SchC := by
  by_cases hc : c = 0
  · subst hc
    have had : a * d = 1 := by simpa using h
    have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one had
    have e : rWR a b 0 d Φ = fun z => (a : ℂ) * (ee (a * b * Complex.normSq z) * Φ ((a : ℂ) * z)) := by
      funext z
      rw [rWR_zero' ha]
      ring
    rw [e]
    exact const_mem _ (chirp_mem _ (dil_mem ha hΦ))
  · have e : rWR a b c d Φ = fun z => (Complex.I * ((-c⁻¹ : ℝ) : ℂ)) * (ee (a / c * Complex.normSq z) *
        Fr (fun u => ee (d / c * Complex.normSq u) * Φ u) (((-c⁻¹ : ℝ) : ℂ) * z)) :=
      funext fun z => rWR_fr' a b d hc Φ z
    rw [e]
    exact const_mem _ (chirp_mem _ (dil_mem (neg_ne_zero.2 (inv_ne_zero hc)) (Fr_mem (chirp_mem _ hΦ))))

def PL (g : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ h : Matrix (Fin 2) (Fin 2) ℝ, h.det = 1 → ∀ Φ ∈ SchC, rWRm (g * h) Φ = rWRm g (rWRm h Φ)

/- English proof (translation)
Rewrite using `[← Matrix.det_fin_two]`. Conclude with `hd`.
-/
theorem det_eq {h : Matrix (Fin 2) (Fin 2) ℝ} (hd : h.det = 1) : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
  rw [← Matrix.det_fin_two]
  exact hd

/- English proof (translation)
The claim follows from `rWR_mem (det_eq hd) hΦ`.
-/
theorem mem_m {h : Matrix (Fin 2) (Fin 2) ℝ} (hd : h.det = 1) {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) : rWRm h Φ ∈ SchC :=
  rWR_mem (det_eq hd) hΦ

/- English proof (translation)
Introduce `h hd Φ _`. Use function extensionality and compare the values at `z`. Use `Pn x _ _ _ _ (det_eq hd) Φ z` as an intermediate fact. Simplify `this` using `[rWRm, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem PL_n (x : ℝ) : PL !![1, x; 0, 1] := by
  intro h hd Φ _
  funext z
  have := Pn x _ _ _ _ (det_eq hd) Φ z
  simpa [rWRm, Matrix.mul_apply, Fin.sum_univ_two] using this

/- English proof (translation)
Introduce `h hd Φ _`. Use function extensionality and compare the values at `z`. Use `Pm hs _ _ _ _ (det_eq hd) Φ z` as an intermediate fact. Simplify `this` using `[rWRm, Matrix.mul_apply, Fin.sum_univ_two, div_eq_inv_mul]`.
-/
theorem PL_m {s : ℝ} (hs : s ≠ 0) : PL !![s, 0; 0, s⁻¹] := by
  intro h hd Φ _
  funext z
  have := Pm hs _ _ _ _ (det_eq hd) Φ z
  simpa [rWRm, Matrix.mul_apply, Fin.sum_univ_two, div_eq_inv_mul] using this

/- English proof (translation)
Introduce `h hd Φ hΦ`. Use function extensionality and compare the values at `z`. Establish `hdd` using `det_eq hd`. Establish `e : rWRm (!![0, 1; -1, 0] * h) Φ z = rWR (h 1 0) (h 1 1) (-h 0 0) (-h 0 1) Φ z`. Simplify using `[rWRm, Matrix.mul_apply, Fin.sum_univ_two]`.

Establish `e2 : rWRm !![0, 1; -1, 0] (rWRm h Φ) z = rWR 0 1 (-1) 0 (rWR (h 0 0) (h 0 1) (h 1 0) (h 1 1) Φ) z`. Simplify using `[rWRm]`. Rewrite using `[e, e2]`. Distinguish the cases in `hc : h 1 0 = 0`. Rewrite `hdd`, the goal using `[hc]`.

Conclude with `Pw0 (by simpa using hdd) Φ z`. Distinguish the cases in `ha : h 0 0 = 0`. Rewrite `hdd`, the goal using `[ha]`. Simplify using `only [neg_zero]`. Conclude with `Pw1 (by linarith) hΦ z`.

Conclude with `Pw2 ha hc hdd hΦ z`.
-/
theorem PL_w : PL !![0, 1; -1, 0] := by
  intro h hd Φ hΦ
  funext z
  have hdd := det_eq hd
  have e : rWRm (!![0, 1; -1, 0] * h) Φ z = rWR (h 1 0) (h 1 1) (-h 0 0) (-h 0 1) Φ z := by
    simp [rWRm, Matrix.mul_apply, Fin.sum_univ_two]
  have e2 : rWRm !![0, 1; -1, 0] (rWRm h Φ) z = rWR 0 1 (-1) 0 (rWR (h 0 0) (h 0 1) (h 1 0) (h 1 1) Φ) z := by
    simp [rWRm]
  rw [e, e2]
  by_cases hc : h 1 0 = 0
  · rw [hc] at hdd ⊢
    exact Pw0 (by simpa using hdd) Φ z
  · by_cases ha : h 0 0 = 0
    · rw [ha] at hdd ⊢
      simp only [neg_zero]
      exact Pw1 (by linarith) hΦ z
    · exact Pw2 ha hc hdd hΦ z

/- English proof (translation)
Introduce `h hh Φ hΦ`. Rewrite using `[Matrix.mul_assoc, hg _ (by rw [Matrix.det_mul, hd, hh, one_mul]) Φ hΦ, hg' h hh Φ hΦ, hg g' hd _ (mem_m hh hΦ)]`.
-/
theorem PL_mul {g g' : Matrix (Fin 2) (Fin 2) ℝ} (hg : PL g) (hg' : PL g') (hd : g'.det = 1) : PL (g * g') := by
  intro h hh Φ hΦ
  rw [Matrix.mul_assoc, hg _ (by rw [Matrix.det_mul, hd, hh, one_mul]) Φ hΦ, hg' h hh Φ hΦ, hg g' hd _ (mem_m hh hΦ)]

/- English proof (translation)
Establish `hdd` using `det_eq hd`. Distinguish the cases in `hc : g 1 0 = 0`. Establish `ha : g 0 0 ≠ 0`. Introduce `ha`. Rewrite `hdd` using `[ha, hc]`.

Simplify using `at hdd`. Establish `hg : g = !![1, g 0 0 * g 0 1; 0, 1] * !![g 0 0, 0; 0, (g 0 0)⁻¹]`. Rewrite `hdd` using `[hc]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc]`.

Clear the denominators using the available nonvanishing facts. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hg]`. Conclude with `PL_mul (PL_n _) (PL_m ha) (by simp [Matrix.det_fin_two, ha])`.

Establish `hg : g = !![1, g 0 0 / g 1 0; 0, 1] * (!![-(g 1 0)⁻¹, 0; 0, (-(g 1 0)⁻¹)⁻¹] * (!![0, 1; -1, 0] * !![1, g 1 1 / g 1 0; 0, 1]))`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> linarith`. Establish `hs : -(g 1 0)⁻¹ ≠ 0` using `neg_ne_zero.2 (inv_ne_zero hc)`. Rewrite using `[hg]`.

Use `PL_mul (PL_n _) (PL_mul (PL_m hs) (PL_mul PL_w (PL_n _) (by simp [Matrix.det_fin_two])) ?_) ?_` and prove the remaining obligations. Simplify using `[Matrix.det_fin_two]`. Simplify using `[Matrix.det_fin_two]`. Clear the denominators using the available nonvanishing facts.
-/
theorem PL_all {g : Matrix (Fin 2) (Fin 2) ℝ} (hd : g.det = 1) : PL g := by
  have hdd := det_eq hd
  by_cases hc : g 1 0 = 0
  · have ha : g 0 0 ≠ 0 := by
      intro ha
      rw [ha, hc] at hdd
      simp at hdd
    have hg : g = !![1, g 0 0 * g 0 1; 0, 1] * !![g 0 0, 0; 0, (g 0 0)⁻¹] := by
      rw [hc] at hdd
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc]
      · field_simp
      · field_simp
        linarith
    rw [hg]
    exact PL_mul (PL_n _) (PL_m ha) (by simp [Matrix.det_fin_two, ha])
  · have hg : g = !![1, g 0 0 / g 1 0; 0, 1] * (!![-(g 1 0)⁻¹, 0; 0, (-(g 1 0)⁻¹)⁻¹] * (!![0, 1; -1, 0] * !![1, g 1 1 / g 1 0; 0, 1])) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> linarith
    have hs : -(g 1 0)⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero hc)
    rw [hg]
    refine PL_mul (PL_n _) (PL_mul (PL_m hs) (PL_mul PL_w (PL_n _) (by simp [Matrix.det_fin_two])) ?_) ?_
    · simp [Matrix.det_fin_two]
    · simp [Matrix.det_fin_two]
      field_simp

/- English proof (translation)
Introduce `g h hg hh Φ hΦ` and use `⟨mem_m hh hΦ, PL_all hg h hh Φ hΦ⟩`.
-/
theorem rwrrep : RWRREP := fun g h hg hh Φ hΦ => ⟨mem_m hh hΦ, PL_all hg h hh Φ hΦ⟩

end GlobalTheory.CompanionTheory.RealWeil
