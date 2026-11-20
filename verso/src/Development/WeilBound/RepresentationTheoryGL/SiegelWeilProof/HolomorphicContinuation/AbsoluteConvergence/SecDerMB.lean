import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerMSt

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

/- English proof (translation)
Introduce `m n A hA F`. Set `Li : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ)` to `(Matrix.toLin' Aᵀ).restrictScalars ℝ`. Set `L : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ)` to `LinearMap.pi fun a => Li.comp (LinearMap.proj a)`. Establish `hL : ∀ y, L y = mulR A y`. Introduce `y`.

Use function extensionality and compare the values at `a j`. Simplify using `[L, Li, mulR, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]`. Establish `hdetLi : LinearMap.det Li = Complex.normSq A.det`. Simplify using `only [Li]`. Rewrite using `[LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, Matrix.det_transpose]`.

Establish `hdet : LinearMap.det L = Complex.normSq A.det ^ m`. Simplify using `only [L, LinearMap.det_pi, hdetLi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Establish `hD : 0 < Complex.normSq A.det ^ m` using `pow_pos (Complex.normSq_pos.2 hA) _`. Establish `hne : LinearMap.det L ≠ 0` using `by rw [hdet]; exact hD.ne'`. Set `Le : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] (Fin m → Fin n → ℂ)` to `LinearMap.equivOfDetNeZero L hne`.

Establish `hH2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Set `e` to `Le.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv`. Establish `he : ∀ y, e y = mulR A y` using `fun y => hL y`. Establish `hmap : Measure.map e (volume : Measure (Fin m → Fin n → ℂ)) = ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume`. Establish `: (e : (Fin m → Fin n → ℂ) → (Fin m → Fin n → ℂ)) = L` using `by funext y; rfl`.

Rewrite using `[this]`. Conclude with `Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne`. Establish `h1 : ∫ y, F (mulR A y) = ((Complex.normSq A.det ^ m)⁻¹ : ℝ) * ∫ x, F x`. Use `integral_map_equiv e F (μ := volume)` as an intermediate fact. Simplify using `only [he] at this`.

Rewrite using `[← this, hmap, integral_smul_measure, hdet, ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.2 hD)]`. Simplify using `[Complex.real_smul]`. Rewrite using `[h1, ← mul_assoc]`. Use `push_cast`. Rewrite using `[mul_inv_cancel₀ (by exact_mod_cast hD.ne'), one_mul]`.
-/
theorem coV : CoV := by
  intro m n A hA F
  let Li : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' Aᵀ).restrictScalars ℝ
  let L : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearMap.pi fun a => Li.comp (LinearMap.proj a)
  have hL : ∀ y, L y = mulR A y := by
    intro y; funext a j
    simp [L, Li, mulR, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
  have hdetLi : LinearMap.det Li = Complex.normSq A.det := by
    simp only [Li]
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, Matrix.det_transpose]
  have hdet : LinearMap.det L = Complex.normSq A.det ^ m := by
    simp only [L, LinearMap.det_pi, hdetLi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hD : 0 < Complex.normSq A.det ^ m := pow_pos (Complex.normSq_pos.2 hA) _
  have hne : LinearMap.det L ≠ 0 := by rw [hdet]; exact hD.ne'
  let Le : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearMap.equivOfDetNeZero L hne
  have hH2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e := Le.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = mulR A y := fun y => hL y
  have hmap : Measure.map e (volume : Measure (Fin m → Fin n → ℂ)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume := by
    have : (e : (Fin m → Fin n → ℂ) → (Fin m → Fin n → ℂ)) = L := by funext y; rfl
    rw [this]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne
  have h1 : ∫ y, F (mulR A y) = ((Complex.normSq A.det ^ m)⁻¹ : ℝ) * ∫ x, F x := by
    have := integral_map_equiv e F (μ := volume)
    simp only [he] at this
    rw [← this, hmap, integral_smul_measure, hdet, ENNReal.toReal_ofReal (abs_nonneg _),
      abs_of_pos (inv_pos.2 hD)]
    simp [Complex.real_smul]
  rw [h1, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hD.ne'), one_mul]

end PositivityTheory.Rg.Sw.AbsSt.SDM
