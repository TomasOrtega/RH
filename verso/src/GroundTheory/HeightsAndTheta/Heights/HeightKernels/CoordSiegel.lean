import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace KCoord

variable {m n : Type*} [Fintype m] [Fintype n]

/- English proof (translation)
Use `PosDef.of_dotProduct_mulVec_pos (hA.1.fromBlocks (by simp) hD.1) fun x hx => ?_` and prove the remaining obligations. Establish `hsplit : star x ⬝ᵥ (fromBlocks A 0 0 D *ᵥ x) = star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr))`. Simplify using `[fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]`. Rewrite using `[hsplit]`. Establish `h1` using `hA.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl)`.

Establish `h2` using `hD.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)`. Distinguish the cases in `hl : x ∘ Sum.inl = 0`. Establish `hr : x ∘ Sum.inr ≠ 0`. Introduce `hr`. Apply `hx` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Consider the cases of `i with`. Consider the case `inl i => exact congrFun hl i`. Consider the case `inr i => exact congrFun hr i`. Use `hD.dotProduct_mulVec_pos hr` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `hA.dotProduct_mulVec_pos hl` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem posDef_fromBlocks_diag {A : Matrix m m ℝ} {D : Matrix n n ℝ} (hA : A.PosDef)
    (hD : D.PosDef) : (fromBlocks A 0 0 D).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (hA.1.fromBlocks (by simp) hD.1) fun x hx => ?_
  have hsplit : star x ⬝ᵥ (fromBlocks A 0 0 D *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
    simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
  rw [hsplit]
  have h1 := hA.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
  have h2 := hD.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
  by_cases hl : x ∘ Sum.inl = 0
  · have hr : x ∘ Sum.inr ≠ 0 := by
      intro hr
      apply hx
      funext i
      cases i with
      | inl i => exact congrFun hl i
      | inr i => exact congrFun hr i
    have := hD.dotProduct_mulVec_pos hr
    linarith
  · have := hA.dotProduct_mulVec_pos hl
    linarith

end KCoord

variable {g : ℕ}

namespace KCoord

def unip (X : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks 1 X 0 1

noncomputable def diagInv (Y : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks Y⁻¹ 0 0 Y

/- English proof (translation)
Establish `hXt : Xᵀ = X` using `hX`. Simplify using `[siegelGram, unip, diagInv, fromBlocks_transpose, fromBlocks_multiply, hXt, add_comm]`.
-/
theorem siegelGram_eq (X Y : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) :
    siegelGram X Y = (unip X)ᵀ * diagInv Y * unip X := by
  have hXt : Xᵀ = X := hX
  simp [siegelGram, unip, diagInv, fromBlocks_transpose, fromBlocks_multiply, hXt, add_comm]

/- English proof (translation)
Establish `hXt : Xᵀ = X` using `hX`. Rewrite using `[SymplecticGroup.mem_iff]`. Simplify using `[unip, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hXt]`.
-/
theorem unip_mem (X : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) :
    unip X ∈ symplecticGroup (Fin g) ℝ := by
  have hXt : Xᵀ = X := hX
  rw [SymplecticGroup.mem_iff]
  simp [unip, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hXt]

/- English proof (translation)
Establish `hdet : IsUnit Y.det` using `(Matrix.isUnit_iff_isUnit_det Y).1 hY.isUnit`. Establish `hYt : Yᵀ = Y`. Use `hY.1` as an intermediate fact. Rewrite `this` using `[Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]`. Then use the resulting hypothesis. Establish `hYit : Y⁻¹ᵀ = Y⁻¹` using `by rw [Matrix.transpose_nonsing_inv, hYt]`.

Rewrite using `[SymplecticGroup.mem_iff]`. Simplify using `[diagInv, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hYt, hYit, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet]`.
-/
theorem diagInv_mem (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) :
    diagInv Y ∈ symplecticGroup (Fin g) ℝ := by
  have hdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).1 hY.isUnit
  have hYt : Yᵀ = Y := by
    have := hY.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hYit : Y⁻¹ᵀ = Y⁻¹ := by rw [Matrix.transpose_nonsing_inv, hYt]
  rw [SymplecticGroup.mem_iff]
  simp [diagInv, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hYt, hYit,
    Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet]

/- English proof (translation)
Rewrite using `[Matrix.isUnit_iff_isUnit_det]`. Simplify using `[unip]`.
-/
theorem unip_isUnit (X : Matrix (Fin g) (Fin g) ℝ) : IsUnit (unip X) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp [unip]

/- English proof (translation)
Rewrite using `[siegelGram_eq X Y hX]`. Use `⟨Submonoid.mul_mem _ (Submonoid.mul_mem _ (SymplecticGroup.transpose_mem (unip_mem X hX)) (diagInv_mem Y hY)) (unip_mem X hX), ?_⟩` and prove the remaining obligations. Establish `hD : (diagInv Y).PosDef` using `posDef_fromBlocks_diag hY.inv hY`. Establish `hinj : Function.Injective (unip X).mulVec` using `Matrix.mulVec_injective_iff_isUnit.mpr (unip_isUnit X)`. Use `hD.conjTranspose_mul_mul_same hinj` as an intermediate fact.

Rewrite `this` using `[Matrix.conjTranspose_eq_transpose_of_trivial]`. Then use the resulting hypothesis.
-/
theorem siegelGram_mem_posDef (X Y : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) (hY : Y.PosDef) :
    siegelGram X Y ∈ symplecticGroup (Fin g) ℝ ∧ (siegelGram X Y).PosDef := by
  rw [siegelGram_eq X Y hX]
  refine ⟨Submonoid.mul_mem _ (Submonoid.mul_mem _
    (SymplecticGroup.transpose_mem (unip_mem X hX)) (diagInv_mem Y hY)) (unip_mem X hX), ?_⟩
  have hD : (diagInv Y).PosDef := posDef_fromBlocks_diag hY.inv hY
  have hinj : Function.Injective (unip X).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr (unip_isUnit X)
  have := hD.conjTranspose_mul_mul_same hinj
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

end KCoord

namespace KCoord

/- English proof (translation)
Establish `hGt : Gᵀ = G`. Use `hG.1` as an intermediate fact. Rewrite `this` using `[Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]`. Then use the resulting hypothesis. Establish `hS'` using `hS`. Rewrite `hS'` using `[SymplecticGroup.mem_iff, hGt]`.

Establish `hGb` using `Matrix.fromBlocks_toBlocks G`. Use `set A := G.toBlocks₁₁ with hAdef`. Use `set B := G.toBlocks₁₂ with hBdef`. Use `set C := G.toBlocks₂₁ with hCdef`. Use `set D := G.toBlocks₂₂ with hDdef`.

Establish `hGt'` using `hGt`. Rewrite `hS'`, `hGt'` using `[← hGb]`. Simplify using `only [fromBlocks_transpose, Matrix.J, fromBlocks_multiply] at hS' hGt'`. Take `⟨e1, e2, -, -⟩` from `Matrix.fromBlocks_inj.mp hS'`. Take `⟨t1, -, t3, -⟩` from `Matrix.fromBlocks_inj.mp hGt'`.

Simplify using `at e1 e2`. Establish `hBA : B * A = A * C`. Use `e1` as an intermediate fact. Rewrite `this` using `[add_neg_eq_zero]`. Then use the resulting hypothesis. Establish `hAD : A * D = 1 + B * B`.

Establish `h1 : A * D = B * B - (B * B + -(A * D))` using `by abel`. Rewrite using `[h1, e2]`. Normalize the expressions using the abelian group laws. Establish `hA : A.PosDef` using `hG.submatrix Sum.inl_injective`. Establish `hAdet : IsUnit A.det` using `(Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit`.

Establish `hAiA : A⁻¹ * A = 1` using `Matrix.nonsing_inv_mul A hAdet`. Establish `hAAi : A * A⁻¹ = 1` using `Matrix.mul_nonsing_inv A hAdet`. Establish `hAit : A⁻¹ᵀ = A⁻¹` using `by rw [Matrix.transpose_nonsing_inv, t1]`. Establish `hCt : Bᵀ = C` using `t3`. Establish `k : A⁻¹ * B = C * A⁻¹`.

Combine the equalities or inequalities in the displayed calculation. Establish `hX : (A⁻¹ * B).IsSymm` using `by show (A⁻¹ * B)ᵀ = A⁻¹ * B`. Rewrite using `[Matrix.transpose_mul, hAit, hCt, k]`. Establish `hY : (A⁻¹).PosDef` using `hA.inv`. Establish `hYinv : (A⁻¹)⁻¹ = A` using `Matrix.nonsing_inv_nonsing_inv A hAdet`.

Use `⟨(A⁻¹ * B, A⁻¹), ⟨hX, hY, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show G = siegelGram (A⁻¹ * B) A⁻¹`. Rewrite using `[siegelGram, hYinv]`. Use `conv_lhs => rw [← hGb]`. Use `congr 1`.

Rewrite using `[← Matrix.mul_assoc, hAAi, Matrix.one_mul]`. Rewrite using `[k, Matrix.mul_assoc, hAiA, Matrix.mul_one]`. Establish `hD : D = A⁻¹ * (1 + B * B)`. Rewrite using `[← hAD, ← Matrix.mul_assoc, hAiA, Matrix.one_mul]`. Rewrite using `[hD, k, Matrix.mul_add, Matrix.mul_one]`.

Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hAAi, Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = C * A⁻¹ * A * A⁻¹ * B := by rw [← k]; simp only [Matrix.mul_assoc]`. Use `_ = C * A⁻¹ * A * (A⁻¹ * B) := by simp only [Matrix.mul_assoc]`.

Use `_ = C * A⁻¹ * A * (C * A⁻¹) := by rw [k]`. Introduce and unpack `⟨X', Y'⟩ ⟨hX', hY', hG'⟩`. Establish `hY'det : IsUnit Y'.det` using `(Matrix.isUnit_iff_isUnit_det Y').1 hY'.isUnit`. Establish `h11 : A = Y'⁻¹`. Rewrite using `[hAdef, hG']`.

Simplify using `[siegelGram]`. Establish `h12 : B = Y'⁻¹ * X'`. Rewrite using `[hBdef, hG']`. Simplify using `[siegelGram]`. Establish `hYY : Y' = A⁻¹`.

Rewrite using `[h11, Matrix.nonsing_inv_nonsing_inv Y' hY'det]`. Establish `hXX : X' = A⁻¹ * B`. Rewrite using `[h12, ← hYY, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv Y' hY'det, Matrix.one_mul]`. Simplify using `only [Prod.mk.injEq]`. Conclude with `⟨hXX, hYY⟩`.
-/
theorem existsUnique_siegelGram (G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ)
    (hS : G ∈ symplecticGroup (Fin g) ℝ) (hG : G.PosDef) :
    ∃! XY : Matrix (Fin g) (Fin g) ℝ × Matrix (Fin g) (Fin g) ℝ,
      XY.1.IsSymm ∧ XY.2.PosDef ∧ G = siegelGram XY.1 XY.2 := by
  have hGt : Gᵀ = G := by
    have := hG.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hS' := hS
  rw [SymplecticGroup.mem_iff, hGt] at hS'
  have hGb := Matrix.fromBlocks_toBlocks G
  set A := G.toBlocks₁₁ with hAdef
  set B := G.toBlocks₁₂ with hBdef
  set C := G.toBlocks₂₁ with hCdef
  set D := G.toBlocks₂₂ with hDdef
  have hGt' := hGt
  rw [← hGb] at hS' hGt'
  simp only [fromBlocks_transpose, Matrix.J, fromBlocks_multiply] at hS' hGt'
  obtain ⟨e1, e2, -, -⟩ := Matrix.fromBlocks_inj.mp hS'
  obtain ⟨t1, -, t3, -⟩ := Matrix.fromBlocks_inj.mp hGt'
  simp at e1 e2
  have hBA : B * A = A * C := by
    have := e1
    rwa [add_neg_eq_zero] at this
  have hAD : A * D = 1 + B * B := by
    have h1 : A * D = B * B - (B * B + -(A * D)) := by abel
    rw [h1, e2]; abel
  have hA : A.PosDef := hG.submatrix Sum.inl_injective
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
  have hAiA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAdet
  have hAAi : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hAdet
  have hAit : A⁻¹ᵀ = A⁻¹ := by rw [Matrix.transpose_nonsing_inv, t1]
  have hCt : Bᵀ = C := t3
  have k : A⁻¹ * B = C * A⁻¹ := by
    calc A⁻¹ * B = A⁻¹ * B * (A * A⁻¹) := by rw [hAAi, Matrix.mul_one]
      _ = A⁻¹ * (B * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * (A * C) * A⁻¹ := by rw [hBA]
      _ = C * A⁻¹ := by rw [← Matrix.mul_assoc A⁻¹ A C, hAiA, Matrix.one_mul]
  have hX : (A⁻¹ * B).IsSymm := by
    show (A⁻¹ * B)ᵀ = A⁻¹ * B
    rw [Matrix.transpose_mul, hAit, hCt, k]
  have hY : (A⁻¹).PosDef := hA.inv
  have hYinv : (A⁻¹)⁻¹ = A := Matrix.nonsing_inv_nonsing_inv A hAdet
  refine ⟨(A⁻¹ * B, A⁻¹), ⟨hX, hY, ?_⟩, ?_⟩
  · show G = siegelGram (A⁻¹ * B) A⁻¹
    rw [siegelGram, hYinv]
    conv_lhs => rw [← hGb]
    congr 1
    · rw [← Matrix.mul_assoc, hAAi, Matrix.one_mul]
    · rw [k, Matrix.mul_assoc, hAiA, Matrix.mul_one]
    · have hD : D = A⁻¹ * (1 + B * B) := by
        rw [← hAD, ← Matrix.mul_assoc, hAiA, Matrix.one_mul]
      rw [hD, k, Matrix.mul_add, Matrix.mul_one]
      congr 1
      calc A⁻¹ * (B * B) = A⁻¹ * B * (A * A⁻¹) * B := by
            rw [hAAi, Matrix.mul_one, Matrix.mul_assoc]
        _ = C * A⁻¹ * A * A⁻¹ * B := by rw [← k]; simp only [Matrix.mul_assoc]
        _ = C * A⁻¹ * A * (A⁻¹ * B) := by simp only [Matrix.mul_assoc]
        _ = C * A⁻¹ * A * (C * A⁻¹) := by rw [k]
  · rintro ⟨X', Y'⟩ ⟨hX', hY', hG'⟩
    have hY'det : IsUnit Y'.det := (Matrix.isUnit_iff_isUnit_det Y').1 hY'.isUnit
    have h11 : A = Y'⁻¹ := by
      rw [hAdef, hG']; simp [siegelGram]
    have h12 : B = Y'⁻¹ * X' := by
      rw [hBdef, hG']; simp [siegelGram]
    have hYY : Y' = A⁻¹ := by
      rw [h11, Matrix.nonsing_inv_nonsing_inv Y' hY'det]
    have hXX : X' = A⁻¹ * B := by
      rw [h12, ← hYY, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv Y' hY'det, Matrix.one_mul]
    simp only [Prod.mk.injEq]
    exact ⟨hXX, hYY⟩

end KCoord

/- English proof (translation)
Introduce `_` and use `⟨fun X Y hX hY => KCoord.siegelGram_mem_posDef X Y hX hY, fun G hS hG => KCoord.existsUnique_siegelGram G hS hG⟩`.
-/
theorem SiegelCoordinates.intersectionNumber_baseChange : SiegelCoordinates.Statement := fun _ =>
  ⟨fun X Y hX hY => KCoord.siegelGram_mem_posDef X Y hX hY,
    fun G hS hG => KCoord.existsUnique_siegelGram G hS hG⟩

end GroundTheory.Heights₂.Heights
