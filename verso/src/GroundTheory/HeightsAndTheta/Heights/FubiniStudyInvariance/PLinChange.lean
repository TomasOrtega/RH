import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ComplexConjugate Matrix ENNReal
open MeasureTheory Set MvPolynomial

noncomputable section

namespace FSInv

open CP

/- English proof (translation)
Introduce `n f hf g hg`. Use `set L := f.restrictScalars ℝ`. Establish `hdet : LinearMap.det L = Complex.normSq (LinearMap.det f)`. Rewrite using `[LinearMap.det_restrictScalars, Algebra.norm_complex_apply]`. Establish `hpos : 0 < Complex.normSq (LinearMap.det f)` using `Complex.normSq_pos.mpr hf`.

Establish `hL : LinearMap.det L ≠ 0` using `by rw [hdet]; exact hpos.ne'`. Establish `hmap` using `Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin n → ℂ)) hL`. Establish `hLm : Measurable L` using `L.continuous_of_finiteDimensional.measurable`. Establish `e : ∫⁻ z, g (f z) = ∫⁻ z, g (L z)` using `rfl`. Rewrite using `[e, ← lintegral_map hg hLm, hmap, lintegral_smul_measure, hdet, abs_inv, abs_of_pos hpos, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one, one_mul]`.
-/
theorem LinChange.proof : LinChange.Statement := by
  intro n f hf g hg
  set L := f.restrictScalars ℝ
  have hdet : LinearMap.det L = Complex.normSq (LinearMap.det f) := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  have hpos : 0 < Complex.normSq (LinearMap.det f) := Complex.normSq_pos.mpr hf
  have hL : LinearMap.det L ≠ 0 := by rw [hdet]; exact hpos.ne'
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin n → ℂ)) hL
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  have e : ∫⁻ z, g (f z) = ∫⁻ z, g (L z) := rfl
  rw [e, ← lintegral_map hg hLm, hmap, lintegral_smul_measure, hdet, abs_inv, abs_of_pos hpos,
    smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne',
    ENNReal.ofReal_one, one_mul]

end FSInv

end

end GroundTheory.Heights₂.Heights
