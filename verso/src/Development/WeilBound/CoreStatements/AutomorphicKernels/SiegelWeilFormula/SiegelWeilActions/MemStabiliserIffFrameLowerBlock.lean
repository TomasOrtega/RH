import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E}

/- English proof (translation)
Take `⟨-, t₀, ht₀⟩` from `hb`. Rewrite using `[GlobalTheory.ThK.Dbl.mem_parabolic_GL2_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht⟩`. Conclude with `((kunf.isPar_frame ht₀ p t).1 ht).1`.

Introduce `h set M := inFrame b p with hM`. Establish `hMi : M * inFrame b p⁻¹ = 1`. Rewrite using `[hM, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, mul_inv_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]`. Establish `hdet : IsUnit M.det` using `Matrix.isUnit_det_of_right_inverse hMi`. Establish `hsplit : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂`.

Rewrite using `[← h, Matrix.fromBlocks_toBlocks]`. Establish `hdet2 : M.det = M.toBlocks₁₁.det * M.toBlocks₂₂.det`. Rewrite using `[hsplit, Matrix.det_fromBlocks_zero₂₁]`. Simplify using `[Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.fromBlocks]`. Establish `hA : IsUnit M.toBlocks₁₁.det` using `isUnit_of_mul_isUnit_left (hdet2 ▸ hdet)`.

Use `set A := M.toBlocks₁₁`. Use `set T0 := incM F t₀.1`. Use `set T0i := incM F (t₀⁻¹).1`. Establish `e1 : T0 * T0i = 1`. Simplify using `only [T0, T0i, incM, ← Matrix.map_mul]`.

Rewrite using `[show t₀.1 * (t₀⁻¹).1 = 1 from t₀.mul_inv]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `e2 : T0i * T0 = 1`. Simplify using `only [T0, T0i, incM, ← Matrix.map_mul]`. Rewrite using `[show (t₀⁻¹).1 * t₀.1 = 1 from t₀.inv_mul]`.

Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hAA : A * A⁻¹ = 1` using `Matrix.mul_nonsing_inv A hA`. Establish `hAA' : A⁻¹ * A = 1` using `Matrix.nonsing_inv_mul A hA`. Set `t : GL (Fin n) (AE F E)` to `⟨T0 * A * T0i, T0 * A⁻¹ * T0i, by`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨t, (kunf.isPar_frame ht₀ p t).2 ⟨h, rfl⟩⟩`.
-/
theorem mem_stabiliser_iff_frame_lower_block (hb : IsFrame2 σ Y b) (p : G2 σ Y) :
    p ∈ par2 σ Y ↔ (inFrame b p).toBlocks₂₁ = 0 := by
  obtain ⟨-, t₀, ht₀⟩ := hb
  rw [GlobalTheory.ThK.Dbl.mem_parabolic_GL2_iff]
  constructor
  · rintro ⟨t, ht⟩
    exact ((kunf.isPar_frame ht₀ p t).1 ht).1
  · intro h
    set M := inFrame b p with hM
    have hMi : M * inFrame b p⁻¹ = 1 := by
      rw [hM, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, mul_inv_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
    have hdet : IsUnit M.det := Matrix.isUnit_det_of_right_inverse hMi
    have hsplit : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
      rw [← h, Matrix.fromBlocks_toBlocks]
    have hdet2 : M.det = M.toBlocks₁₁.det * M.toBlocks₂₂.det := by
      rw [hsplit, Matrix.det_fromBlocks_zero₂₁]
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.fromBlocks]
    have hA : IsUnit M.toBlocks₁₁.det := isUnit_of_mul_isUnit_left (hdet2 ▸ hdet)
    set A := M.toBlocks₁₁
    set T0 := incM F t₀.1
    set T0i := incM F (t₀⁻¹).1
    have e1 : T0 * T0i = 1 := by
      simp only [T0, T0i, incM, ← Matrix.map_mul]
      rw [show t₀.1 * (t₀⁻¹).1 = 1 from t₀.mul_inv]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have e2 : T0i * T0 = 1 := by
      simp only [T0, T0i, incM, ← Matrix.map_mul]
      rw [show (t₀⁻¹).1 * t₀.1 = 1 from t₀.inv_mul]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
    have hAA' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
    let t : GL (Fin n) (AE F E) := ⟨T0 * A * T0i, T0 * A⁻¹ * T0i, by
        calc T0 * A * T0i * (T0 * A⁻¹ * T0i) = T0 * (A * (T0i * T0) * A⁻¹) * T0i := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [e2, Matrix.mul_one, hAA, Matrix.mul_one, e1], by
        calc T0 * A⁻¹ * T0i * (T0 * A * T0i) = T0 * (A⁻¹ * (T0i * T0) * A) * T0i := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [e2, Matrix.mul_one, hAA', Matrix.mul_one, e1]⟩
    exact ⟨t, (kunf.isPar_frame ht₀ p t).2 ⟨h, rfl⟩⟩

end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

end
