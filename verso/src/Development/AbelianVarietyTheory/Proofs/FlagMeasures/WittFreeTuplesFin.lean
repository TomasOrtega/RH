import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFieldOrExistsSwappedIdempotentOfQuadraticEtaleStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionHermitianFramesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittFreeTuplesSplitQuadraticEtaleStatement

open GlobalTheory.SgAlg Matrix

namespace GlobalTheory

/- English proof (translation)
Break down `GlobalTheory.T.isField_or_exists_swapped_idempotent_of_quadraticEtale σ hσ with hF | hS` into its components or cases. Use `letI := hF.toField`. Conclude with `GlobalTheory.T.witt_extension_hermitian_frames σ hσ J hJ Y Y' hY hY' hP`. Conclude with `GlobalTheory.T.witt_free_tuples_split_quadratic_etale σ hσ hS J hJ Y Y' hY hY' hP`.
-/
theorem witt_free_tuples_fin {E : Type} [CommRing E] (σ : E →+* E) (hσ : IsQA σ) {n k : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermU σ J) (Y Y' : Matrix (Fin n) (Fin k) E)
    (hY : Free Y) (hY' : Free Y') (hP : pairM σ J Y Y = pairM σ J Y' Y') :
    ∃ g, IsUn σ J g ∧ g * Y = Y' := by
  rcases GlobalTheory.T.isField_or_exists_swapped_idempotent_of_quadraticEtale σ hσ with hF | hS
  · letI := hF.toField
    exact GlobalTheory.T.witt_extension_hermitian_frames σ hσ J hJ Y Y' hY hY' hP
  · exact GlobalTheory.T.witt_free_tuples_split_quadratic_etale σ hσ hS J hJ Y Y' hY hY' hP

/- English proof (translation)
Take `⟨L, hL⟩` from `hX`. Use `⟨L.submatrix e id, ?_⟩` and prove the remaining obligations. Establish `h : L.submatrix e id * X.submatrix id e = (L * X).submatrix e e`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`.

Rewrite using `[h, hL]`. Simplify using the standard rewrite rules.
-/
theorem free_reindex {E : Type} [CommRing E] {n : ℕ} {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : b ≃ a) {X : Matrix (Fin n) a E} (hX : Free X) :
    Free (X.submatrix id e) := by
  obtain ⟨L, hL⟩ := hX
  refine ⟨L.submatrix e id, ?_⟩
  have h : L.submatrix e id * X.submatrix id e = (L * X).submatrix e e := by
    ext i j
    simp [Matrix.mul_apply]
  rw [h, hL]
  simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[pairM, cT, Matrix.mul_apply]`.
-/
theorem pairM_reindex {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} {a b : Type} [Fintype a]
    (e : b ≃ a) (J : Matrix (Fin n) (Fin n) E) (X X' : Matrix (Fin n) a E) :
    pairM σ J (X'.submatrix id e) (X.submatrix id e) = (pairM σ J X' X).submatrix e e := by
  ext i j
  simp [pairM, cT, Matrix.mul_apply]

/- English proof (translation)
Set `e : Fin (Fintype.card a) ≃ a` to `(Fintype.equivFin a).symm`. Take `⟨g, hg, hgX⟩` from `witt_free_tuples_fin σ hσ J hJ (X.submatrix id e) (X'.submatrix id e) (free_reindex e hX) (free_reindex e hX') (by rw [pairM_reindex, pairM_reindex, hP])`. Use `⟨g, hg, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `h` using `congrFun (congrFun hgX i) (e.symm j)`.

Simplify `h` using `[Matrix.mul_apply]`.
-/
theorem witt_free_tuples {E : Type} [CommRing E] (σ : E →+* E) (hσ : IsQA σ) {n : ℕ} {a : Type}
    [Fintype a] [DecidableEq a] (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermU σ J)
    (X X' : Matrix (Fin n) a E) (hX : Free X) (hX' : Free X')
    (hP : pairM σ J X X = pairM σ J X' X') : ∃ g, IsUn σ J g ∧ g * X = X' := by
  let e : Fin (Fintype.card a) ≃ a := (Fintype.equivFin a).symm
  obtain ⟨g, hg, hgX⟩ := witt_free_tuples_fin σ hσ J hJ (X.submatrix id e) (X'.submatrix id e)
    (free_reindex e hX) (free_reindex e hX')
    (by rw [pairM_reindex, pairM_reindex, hP])
  refine ⟨g, hg, ?_⟩
  ext i j
  have h := congrFun (congrFun hgX i) (e.symm j)
  simpa [Matrix.mul_apply] using h

end GlobalTheory
