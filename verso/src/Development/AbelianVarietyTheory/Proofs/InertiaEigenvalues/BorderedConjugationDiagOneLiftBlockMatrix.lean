import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Step.ActEmbLift

/- English proof (translation)
Simplify using `only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, full, Matrix.reindex_apply]`. Rewrite using `[Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Use `congr 2`. Simplify using the standard rewrite rules. Use extensionality with `i j`.

Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.vecMul, dotProduct]`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`.
-/
theorem embHom_mul_full_mul (k : Type) [CommRing k] (r : ℕ) (g h : Matrix (Fin r) (Fin r) k) (Z : Gl r k) :
    embHom r k g * full Z * embHom r k h = full (g * Z.1 * h, g *ᵥ Z.2.1, Z.2.2.1 ᵥ* h, Z.2.2.2) := by
  simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, full, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 2
  · simp
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply]

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, eL, Matrix.reindex_apply]`. Rewrite using `[Matrix.mulVec_single_one]`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `[Matrix.transpose_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last]`.

Simplify using `[Matrix.transpose_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc]`.
-/
theorem embHom_mulVec_eL (k : Type) [CommRing k] (r : ℕ) (g : Matrix (Fin r) (Fin r) k) :
    embHom r k g *ᵥ eL r k = eL r k := by
  ext i
  simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, eL, Matrix.reindex_apply]
  rw [Matrix.mulVec_single_one]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Matrix.transpose_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last]
  · simp [Matrix.transpose_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc]

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, eL, Matrix.reindex_apply]`. Rewrite using `[Matrix.single_one_vecMul]`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `[Matrix.submatrix_apply, finSumFinEquiv_symm_last]`.

Simplify using `[Matrix.submatrix_apply, finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc]`.
-/
theorem eL_vecMul_embHom (k : Type) [CommRing k] (r : ℕ) (g : Matrix (Fin r) (Fin r) k) :
    eL r k ᵥ* embHom r k g = eL r k := by
  ext i
  simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, eL, Matrix.reindex_apply]
  rw [Matrix.single_one_vecMul]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Matrix.submatrix_apply, finSumFinEquiv_symm_last]
  · simp [Matrix.submatrix_apply, finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc]

/- English proof (translation)
Establish `hinv : ((emb r k g)⁻¹ : GL (Fin (r + 1)) k) = emb r k g⁻¹` using `(map_inv _ _).symm`. Simplify using `only [act, lift, hinv, emb, Units.coe_map, MonoidHom.coe_coe]`. Use `Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))` and prove the remaining obligations. Conclude with `embHom_mul_full_mul k r _ _ Z`. Simplify using `only [Matrix.mulVec_smul, embHom_mulVec_eL]`.

Conclude with `eL_vecMul_embHom k r _`.
-/
theorem act_emb_lift (k : Type) [CommRing k] (r : ℕ) (g : GL (Fin r) k) (Z : Gl r k) (μ l : k) :
    act (GlobalTheory.JR.Step.emb r k g) (GlobalTheory.JR.Step.lift Z μ l) = GlobalTheory.JR.Step.lift (act g Z) μ l := by
  have hinv : ((emb r k g)⁻¹ : GL (Fin (r + 1)) k) = emb r k g⁻¹ := (map_inv _ _).symm
  simp only [act, lift, hinv, emb, Units.coe_map, MonoidHom.coe_coe]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · exact embHom_mul_full_mul k r _ _ Z
  · simp only [Matrix.mulVec_smul, embHom_mulVec_eL]
  · exact eL_vecMul_embHom k r _

end GlobalTheory.JR.Step.ActEmbLift
