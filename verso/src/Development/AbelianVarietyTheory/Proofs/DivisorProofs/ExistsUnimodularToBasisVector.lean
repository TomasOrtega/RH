import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open GlobalTheory.TriFrame

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ r a l0 ha`. Use `set σ : Equiv.Perm (Fin (r+1)) := Equiv.swap 0 l0 with hσ`. Use `set b : Fin (r+1) → R := a ∘ σ with hb`. Use `set E : Matrix (Fin (r+1)) (Fin (r+1)) R := Matrix.of fun l j => if j = 0 then b l else if l = j then 1 else 0 with hEdef`. Establish `hlow : E.BlockTriangular OrderDual.toDual`.

Introduce `i j hij`. Establish `hij' : i < j` using `hij`. Establish `hj : j ≠ 0`. Introduce and unpack `rfl`. Conclude with `absurd hij' (Fin.not_lt_zero i)`.

Establish `hne : i ≠ j` using `ne_of_lt hij'`. Simplify using `[hEdef, hj, hne]`. Establish `hE : E.det = b 0`. Rewrite using `[Matrix.det_of_lowerTriangular E hlow, Fin.prod_univ_succ]`. Establish `: ∀ i : Fin r, E i.succ i.succ = 1`.

Introduce `i`. Simplify using `[hEdef, Fin.succ_ne_zero]`. Simplify using `[this, hEdef]`. Use `set B : Matrix (Fin (r+1)) (Fin (r+1)) R := E.submatrix σ id with hBdef`. Establish `hBdet : IsUnit B.det`.

Rewrite using `[hBdef, Matrix.det_permute, hE]`. Establish `h0 : b 0 = a l0` using `by simp [hb, hσ]`. Rewrite using `[h0]`. Use `IsUnit.mul ?_ ha` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]`.

Establish `hBcol : B.mulVec (Pi.single 0 1) = a`. Use function extensionality and compare the values at `i`. Simplify using `[hBdef, hEdef, Matrix.mulVec, dotProduct, Pi.single_apply, hb, hσ]`. Take `⟨u, hu⟩` from `(Matrix.isUnit_iff_isUnit_det B).mpr hBdet`. Use `⟨u⁻¹, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hBcol, Matrix.mulVec_mulVec, ← hu]`. Establish `: ((u⁻¹ : GL (Fin (r+1)) R) : Matrix (Fin (r+1)) (Fin (r+1)) R) * (u : Matrix _ _ R) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Rewrite using `[this, Matrix.one_mulVec]`.
-/
theorem column_unit_entry_to_first_basis_vector :
    ∀ {R : Type} [CommRing R] {r : ℕ} (a : Fin (r+1) → R) (l0 : Fin (r+1)), IsUnit (a l0) →
      ∃ Q : GL (Fin (r+1)) R, (Q : Matrix (Fin (r+1)) (Fin (r+1)) R).mulVec a
        = (Pi.single 0 1 : Fin (r+1) → R) := by
  intro R _ r a l0 ha
  classical
  set σ : Equiv.Perm (Fin (r+1)) := Equiv.swap 0 l0 with hσ
  set b : Fin (r+1) → R := a ∘ σ with hb
  set E : Matrix (Fin (r+1)) (Fin (r+1)) R :=
    Matrix.of fun l j => if j = 0 then b l else if l = j then 1 else 0 with hEdef
  have hlow : E.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    have hj : j ≠ 0 := by
      rintro rfl
      exact absurd hij' (Fin.not_lt_zero i)
    have hne : i ≠ j := ne_of_lt hij'
    simp [hEdef, hj, hne]
  have hE : E.det = b 0 := by
    rw [Matrix.det_of_lowerTriangular E hlow, Fin.prod_univ_succ]
    have : ∀ i : Fin r, E i.succ i.succ = 1 := by
      intro i
      simp [hEdef, Fin.succ_ne_zero]
    simp [this, hEdef]
  set B : Matrix (Fin (r+1)) (Fin (r+1)) R := E.submatrix σ id with hBdef
  have hBdet : IsUnit B.det := by
    rw [hBdef, Matrix.det_permute, hE]
    have h0 : b 0 = a l0 := by simp [hb, hσ]
    rw [h0]
    refine IsUnit.mul ?_ ha
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hBcol : B.mulVec (Pi.single 0 1) = a := by
    funext i
    simp [hBdef, hEdef, Matrix.mulVec, dotProduct, Pi.single_apply, hb, hσ]
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det B).mpr hBdet
  refine ⟨u⁻¹, ?_⟩
  rw [← hBcol, Matrix.mulVec_mulVec, ← hu]
  have : ((u⁻¹ : GL (Fin (r+1)) R) : Matrix (Fin (r+1)) (Fin (r+1)) R) * (u : Matrix _ _ R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [this, Matrix.one_mulVec]

end GlobalTheory
