import Mathlib

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.EisTube

universe u

/- English proof (translation)
Simplify using `[PiLp.inner_apply, mul_comm]`.
-/
theorem inner_eq_sum_coord {ι : Type} [Fintype ι] (v w : EuclideanSpace ℝ ι) :
    ⟪v, w⟫ = ∑ i, v i * w i := by
  simp [PiLp.inner_apply, mul_comm]

/- English proof (translation)
Introduce `ι _ g hgc hgi hFi y`. Use `set F : (ι → ℝ) → ℂ := fun t => ∫ y, g y * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i) with hF`. Set `f : EuclideanSpace ℝ ι → ℂ` to `fun v => g (WithLp.ofLp v)`. Establish `mp` using `PiLp.volume_preserving_ofLp ι`. Establish `memb : MeasurableEmbedding (@WithLp.ofLp 2 (ι → ℝ))` using `(MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurableEmbedding`.

Establish `hfc : Continuous f` using `hgc.comp (PiLp.continuous_ofLp 2 _)`. Establish `hfi : Integrable f` using `(mp.integrable_comp hgi.aestronglyMeasurable).2 hgi`. Establish `hFou : ∀ v : EuclideanSpace ℝ ι, 𝓕 f v = F (WithLp.ofLp v)`. Introduce `v`. Rewrite using `[Real.fourier_eq']`.

Simplify using `only [hF]`. Rewrite using `[← mp.integral_comp memb]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Simplify using `only [smul_eq_mul, f]`. Rewrite using `[mul_comm]`.

Use `congr 2`. Rewrite using `[inner_eq_sum_coord]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hFfun : 𝓕 f = fun v => F (WithLp.ofLp v)` using `funext hFou`.

Establish `hFi' : Integrable (𝓕 f)`. Rewrite using `[hFfun]`. Conclude with `(mp.integrable_comp hFi.aestronglyMeasurable).2 hFi`. Establish `hinv : 𝓕⁻ (𝓕 f) = f` using `Continuous.fourierInv_fourier_eq hfc hfi hFi'`. Establish `h` using `congrFun hinv (WithLp.toLp 2 y)`.

Rewrite `h` using `[Real.fourierInv_eq', hFfun]`. Establish `h2 : ∫ t : ι → ℝ, F t * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i) = ∫ v : EuclideanSpace ℝ ι, Complex.exp (((2 * Real.pi * ⟪v, WithLp.toLp 2 y⟫ : ℝ) : ℂ) * Complex.I) • F (WithLp.ofLp v)`. Rewrite using `[← mp.integral_comp memb]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`.

Rewrite using `[mul_comm]`. Use `congr 2`. Rewrite using `[inner_eq_sum_coord]`. Use `push_cast`. Simplify using `only [mul_comm]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `h2.trans h`.
-/
theorem fourierInvCoord : ∀ (ι : Type) [Fintype ι] (g : (ι → ℝ) → ℂ), Continuous g → MeasureTheory.Integrable g →
    MeasureTheory.Integrable (fun t : ι → ℝ =>
      ∫ y, g y * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i)) →
    ∀ y : ι → ℝ, (∫ t : ι → ℝ, (∫ y', g y' * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y' i : ℂ) * t i)) *
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i)) = g y := by
  intro ι _ g hgc hgi hFi y
  set F : (ι → ℝ) → ℂ := fun t =>
    ∫ y, g y * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i) with hF
  let f : EuclideanSpace ℝ ι → ℂ := fun v => g (WithLp.ofLp v)
  have mp := PiLp.volume_preserving_ofLp ι
  have memb : MeasurableEmbedding (@WithLp.ofLp 2 (ι → ℝ)) :=
    (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurableEmbedding
  have hfc : Continuous f := hgc.comp (PiLp.continuous_ofLp 2 _)
  have hfi : Integrable f := (mp.integrable_comp hgi.aestronglyMeasurable).2 hgi
  have hFou : ∀ v : EuclideanSpace ℝ ι, 𝓕 f v = F (WithLp.ofLp v) := by
    intro v
    rw [Real.fourier_eq']
    simp only [hF]
    rw [← mp.integral_comp memb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [smul_eq_mul, f]
    rw [mul_comm]
    congr 2
    rw [inner_eq_sum_coord]
    push_cast
    ring
  have hFfun : 𝓕 f = fun v => F (WithLp.ofLp v) := funext hFou
  have hFi' : Integrable (𝓕 f) := by
    rw [hFfun]
    exact (mp.integrable_comp hFi.aestronglyMeasurable).2 hFi
  have hinv : 𝓕⁻ (𝓕 f) = f := Continuous.fourierInv_fourier_eq hfc hfi hFi'
  have h := congrFun hinv (WithLp.toLp 2 y)
  rw [Real.fourierInv_eq', hFfun] at h
  have h2 : ∫ t : ι → ℝ, F t * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i) =
      ∫ v : EuclideanSpace ℝ ι, Complex.exp (((2 * Real.pi * ⟪v, WithLp.toLp 2 y⟫ : ℝ) : ℂ) * Complex.I) •
        F (WithLp.ofLp v) := by
    rw [← mp.integral_comp memb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [smul_eq_mul]
    rw [mul_comm]
    congr 2
    rw [inner_eq_sum_coord]
    push_cast
    simp only [mul_comm]
    ring
  exact h2.trans h

end GlobalTheory.CompanionTheory.EisTube
