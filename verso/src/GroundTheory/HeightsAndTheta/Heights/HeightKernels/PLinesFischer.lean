import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix
open scoped ComplexOrder

namespace KLinesFischer

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [toBlocks₂₁, toBlocks₁₂, conjTranspose_apply, of_apply]`. Conclude with `(hM.apply (Sum.inr i) (Sum.inl j)).symm`.
-/
theorem toBlocks₂₁_eq {m k : Type*} {M : Matrix (m ⊕ k) (m ⊕ k) ℂ} (hM : M.IsHermitian) :
    M.toBlocks₂₁ = M.toBlocks₁₂ᴴ := by
  ext i j
  simp only [toBlocks₂₁, toBlocks₁₂, conjTranspose_apply, of_apply]
  exact (hM.apply (Sum.inr i) (Sum.inl j)).symm

end KLinesFischer

/- English proof (translation)
Introduce `m k _ _ _ _ M hM`. Establish `hA : M.toBlocks₁₁.PosDef` using `hM.submatrix (e := (Sum.inl : m → m ⊕ k)) Sum.inl_injective`. Establish `hApos : 0 < M.toBlocks₁₁.det.re` using `MCDet.re_det_pos hA`. Establish `hdet0 : M.toBlocks₁₁.det ≠ 0` using `fun h => by simp [h] at hApos`. Set `_ : Invertible M.toBlocks₁₁` to `invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hdet0)`.

Establish `hMe : M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₁₂ᴴ M.toBlocks₂₂`. Rewrite using `[← KLinesFischer.toBlocks₂₁_eq hM.1]`. Conclude with `(fromBlocks_toBlocks M).symm`. Establish `hS : (M.toBlocks₂₂ - M.toBlocks₁₂ᴴ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂).PosSemidef`. Establish `h` using `hM.posSemidef`.

Rewrite `h` using `[hMe]`. Conclude with `(PosDef.fromBlocks₁₁ _ _ hA).mp h`. Establish `hdet : M.det = M.toBlocks₁₁.det * (M.toBlocks₂₂ - M.toBlocks₁₂ᴴ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂).det` using `by conv_lhs => rw [hMe]`. Rewrite using `[det_fromBlocks₁₁, invOf_eq_nonsing_inv]`. Establish `hmono : (M.toBlocks₂₂ - M.toBlocks₁₂ᴴ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂).det.re ≤ M.toBlocks₂₂.det.re`.

Use `MCDet.re_det_mono hS ?_` and prove the remaining obligations. Rewrite using `[sub_sub_cancel]`. Conclude with `hA.posSemidef.inv.conjTranspose_mul_mul_same _`. Establish `him : M.toBlocks₁₁.det.im = 0`. Establish `h` using `congrArg Complex.im (MCDet.det_eq_ofReal_re hA.posSemidef)`.

Simplify using `using h`. Rewrite using `[hdet, Complex.mul_re, him, zero_mul, sub_zero]`. Conclude with `mul_le_mul_of_nonneg_left hmono hApos.le`.
-/
theorem LinesFischer.proof : LinesFischer.Statement := by
  intro m k _ _ _ _ M hM
  have hA : M.toBlocks₁₁.PosDef := hM.submatrix (e := (Sum.inl : m → m ⊕ k)) Sum.inl_injective
  have hApos : 0 < M.toBlocks₁₁.det.re := MCDet.re_det_pos hA
  have hdet0 : M.toBlocks₁₁.det ≠ 0 := fun h => by simp [h] at hApos
  let _ : Invertible M.toBlocks₁₁ := invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hdet0)
  have hMe : M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₁₂ᴴ M.toBlocks₂₂ := by
    rw [← KLinesFischer.toBlocks₂₁_eq hM.1]
    exact (fromBlocks_toBlocks M).symm
  have hS : (M.toBlocks₂₂ - M.toBlocks₁₂ᴴ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂).PosSemidef := by
    have h := hM.posSemidef
    rw [hMe] at h
    exact (PosDef.fromBlocks₁₁ _ _ hA).mp h
  have hdet : M.det = M.toBlocks₁₁.det *
      (M.toBlocks₂₂ - M.toBlocks₁₂ᴴ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂).det := by
    conv_lhs => rw [hMe]
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hmono : (M.toBlocks₂₂ - M.toBlocks₁₂ᴴ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂).det.re ≤
      M.toBlocks₂₂.det.re := by
    refine MCDet.re_det_mono hS ?_
    rw [sub_sub_cancel]
    exact hA.posSemidef.inv.conjTranspose_mul_mul_same _
  have him : M.toBlocks₁₁.det.im = 0 := by
    have h := congrArg Complex.im (MCDet.det_eq_ofReal_re hA.posSemidef)
    simpa using h
  rw [hdet, Complex.mul_re, him, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left hmono hApos.le

end GroundTheory.Heights₂.Heights
