import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.BergmanSt
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Matrix
open scoped ComplexOrder

variable {X : Type*} [MeasurableSpace X]

noncomputable def wPath (w₀ u : X → ℝ) (a t : ℝ) (x : X) : ℝ :=
  w₀ x * Real.exp (-(t * a * u x))

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [conjTranspose_apply, bGram, of_apply, Complex.star_def]`. Rewrite using `[← integral_conj]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Simplify using `only [map_mul, Complex.conj_conj, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma bGram_isHermitian (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) :
    (bGram μ s w).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, bGram, of_apply, Complex.star_def]
  rw [← integral_conj]
  congr 1; funext x
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

/- English proof (translation)
Rewrite using `[bNormSq_eq μ s w hint c]`. Simplify using `only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma dot_bGram (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ)
    (c : Fin r → ℂ) : star c ⬝ᵥ (bGram μ s w *ᵥ c) = (bNormSq μ s w c : ℂ) := by
  rw [bNormSq_eq μ s w hint c]
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish `h : ((‖∑ i, c i * s i x‖ ^ 2 * w x : ℝ) : ℂ) = ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (starRingEnd ℂ (s i x) * s j x * (w x : ℂ))`. Use `push_cast`. Rewrite using `[← Complex.conj_mul', map_sum, Finset.sum_mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h, Complex.ofReal_re]`.
-/
lemma normSq_mul_eq {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) (c : Fin r → ℂ) (x : X) :
    ‖∑ i, c i * s i x‖ ^ 2 * w x =
      (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (starRingEnd ℂ (s i x) * s j x * (w x : ℂ))).re := by
  have h : ((‖∑ i, c i * s i x‖ ^ 2 * w x : ℝ) : ℂ) =
      ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) := by
    push_cast
    rw [← Complex.conj_mul', map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul]; ring
  rw [← h, Complex.ofReal_re]

/- English proof (translation)
Establish `hF : Integrable (fun x => ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (starRingEnd ℂ (s i x) * s j x * (w x : ℂ))) μ` using `integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _`. Conclude with `hF.re.congr (Filter.Eventually.of_forall fun x => (normSq_mul_eq s w c x).symm)`.
-/
lemma integrable_normSq_mul (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ)
    (c : Fin r → ℂ) : Integrable (fun x => ‖∑ i, c i * s i x‖ ^ 2 * w x) μ := by
  have hF : Integrable (fun x => ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      (starRingEnd ℂ (s i x) * s j x * (w x : ℂ))) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _
  exact hF.re.congr (Filter.Eventually.of_forall fun x => (normSq_mul_eq s w c x).symm)

end ReciprocityTheory.GeometryOfNumbersTheory
