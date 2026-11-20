import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.CayleyRat

/- English proof (translation)
Introduce `L _ _ _ n S hS hdet`. Use `set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc`. Use `set T : Matrix (Fin n) (Fin n) L := 1 - S with hT`. Use `set U : Matrix (Fin n) (Fin n) L := 1 + S with hU`. Establish `hSc : conjT c S = -S`.

Unfold `conjT`. Conclude with `(neg_eq_of_add_eq_zero_right hS).symm`. Establish `hcT : conjT c T = U`. Establish `: conjT c T = conjT c 1 - conjT c S`. Simplify using `[conjT, hT, Matrix.map_sub, Matrix.transpose_sub]`.

Rewrite using `[this, conjT_one, hSc, hU, sub_neg_eq_add]`. Establish `hcU : conjT c U = T`. Establish `: conjT c U = conjT c 1 + conjT c S`. Simplify using `[conjT, hU, Matrix.map_add, Matrix.transpose_add]`. Rewrite using `[this, conjT_one, hSc, hT, sub_eq_add_neg]`.

Establish `hdetU : U.det ≠ 0`. Establish `: U.det = c T.det`. Rewrite using `[← hcT, conjT, Matrix.det_transpose, RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `(map_ne_zero c).mpr hdet`. Establish `huT : IsUnit T.det` using `isUnit_iff_ne_zero.mpr hdet`. Establish `huU : IsUnit U.det` using `isUnit_iff_ne_zero.mpr hdetU`. Establish `hcTinv : conjT c T⁻¹ = U⁻¹`. Establish `h1 : U * conjT c T⁻¹ = 1`.

Rewrite using `[← hcT, ← conjT_mul, Matrix.nonsing_inv_mul _ huT, conjT_one]`. Conclude with `(Matrix.inv_eq_right_inv h1).symm`. Establish `hcomm : U * T = T * U`. Simplify using `[hU, hT, mul_sub, sub_mul, mul_add, add_mul]`. Normalize the expressions using the abelian group laws.

Establish `hinv : T⁻¹ * U⁻¹ = U⁻¹ * T⁻¹`. Rewrite using `[← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, hcomm]`. Establish `hdetγ : IsUnit (U * T⁻¹).det`. Rewrite using `[Matrix.det_mul]`. Conclude with `huU.mul (Matrix.isUnit_nonsing_inv_det T huT)`.

Use `⟨Matrix.nonsingInvUnit (U * T⁻¹) hdetγ, ?_, rfl⟩` and prove the remaining obligations. Use `show (U * T⁻¹) * conjT c (U * T⁻¹) = 1`. Rewrite using `[conjT_mul, hcTinv, hcU, Matrix.mul_assoc, ← Matrix.mul_assoc T⁻¹, hinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huU, Matrix.one_mul, Matrix.nonsing_inv_mul _ huT]`.
-/
theorem exists_mem_GQ0_eq_cayley_of_skew_hermitian : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (S : Matrix (Fin n) (Fin n) L), S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 → (1 - S).det ≠ 0 → ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ (γ₀ : Matrix (Fin n) (Fin n) L) = (1 + S) * (1 - S)⁻¹ := by
  intro L _ _ _ n S hS hdet
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  set T : Matrix (Fin n) (Fin n) L := 1 - S with hT
  set U : Matrix (Fin n) (Fin n) L := 1 + S with hU
  have hSc : conjT c S = -S := by
    unfold conjT; exact (neg_eq_of_add_eq_zero_right hS).symm
  have hcT : conjT c T = U := by
    have : conjT c T = conjT c 1 - conjT c S := by
      simp [conjT, hT, Matrix.map_sub, Matrix.transpose_sub]
    rw [this, conjT_one, hSc, hU, sub_neg_eq_add]
  have hcU : conjT c U = T := by
    have : conjT c U = conjT c 1 + conjT c S := by
      simp [conjT, hU, Matrix.map_add, Matrix.transpose_add]
    rw [this, conjT_one, hSc, hT, sub_eq_add_neg]
  have hdetU : U.det ≠ 0 := by
    have : U.det = c T.det := by
      rw [← hcT, conjT, Matrix.det_transpose, RingHom.map_det]; rfl
    rw [this]; exact (map_ne_zero c).mpr hdet
  have huT : IsUnit T.det := isUnit_iff_ne_zero.mpr hdet
  have huU : IsUnit U.det := isUnit_iff_ne_zero.mpr hdetU
  have hcTinv : conjT c T⁻¹ = U⁻¹ := by
    have h1 : U * conjT c T⁻¹ = 1 := by
      rw [← hcT, ← conjT_mul, Matrix.nonsing_inv_mul _ huT, conjT_one]
    exact (Matrix.inv_eq_right_inv h1).symm
  have hcomm : U * T = T * U := by
    simp [hU, hT, mul_sub, sub_mul, mul_add, add_mul]; abel
  have hinv : T⁻¹ * U⁻¹ = U⁻¹ * T⁻¹ := by
    rw [← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, hcomm]
  have hdetγ : IsUnit (U * T⁻¹).det := by
    rw [Matrix.det_mul]; exact huU.mul (Matrix.isUnit_nonsing_inv_det T huT)
  refine ⟨Matrix.nonsingInvUnit (U * T⁻¹) hdetγ, ?_, rfl⟩
  show (U * T⁻¹) * conjT c (U * T⁻¹) = 1
  rw [conjT_mul, hcTinv, hcU, Matrix.mul_assoc, ← Matrix.mul_assoc T⁻¹, hinv, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huU, Matrix.one_mul, Matrix.nonsing_inv_mul _ huT]

end GlobalTheory.CayleyRat
