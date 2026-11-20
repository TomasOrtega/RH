import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GzNeOfTotPos

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.DetGa

open Matrix

section General

variable {R : Type*} [CommRing R] {k : ℕ}

def cornerM (k : ℕ) (s : R) : Matrix (Fin (k + 1)) (Fin (k + 1)) R :=
  Matrix.of fun a b => if a = Fin.last k ∧ b = Fin.last k then s else 0

/- English proof (translation)
Rewrite using `[Matrix.det_succ_row _ (Fin.last k), Finset.sum_eq_single (Fin.last k)]`. Establish `hs : (A.updateRow (Fin.last k) (Pi.single (Fin.last k) 1)).submatrix (Fin.last k).succAbove (Fin.last k).succAbove = A.submatrix Fin.castSucc Fin.castSucc`. Use extensionality with `i j`. Simplify using `[Fin.succAbove_last, Matrix.updateRow_ne (Fin.castSucc_lt_last i).ne]`. Rewrite using `[hs]`.

Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Pi.single_apply, hj]`. Simplify using the standard rewrite rules.
-/
theorem det_updateRow_last_single (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    (A.updateRow (Fin.last k) (Pi.single (Fin.last k) 1)).det = (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row _ (Fin.last k), Finset.sum_eq_single (Fin.last k)]
  · have hs : (A.updateRow (Fin.last k) (Pi.single (Fin.last k) 1)).submatrix (Fin.last k).succAbove
        (Fin.last k).succAbove = A.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp [Fin.succAbove_last, Matrix.updateRow_ne (Fin.castSucc_lt_last i).ne]
    rw [hs]
    simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp

/- English proof (translation)
The claim follows from `Matrix.det_eq_zero_of_row_eq_zero (Fin.last k) fun j => by simp`.
-/
theorem det_updateRow_last_zero (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    (A.updateRow (Fin.last k) 0).det = 0 :=
  Matrix.det_eq_zero_of_row_eq_zero (Fin.last k) fun j => by simp

/- English proof (translation)
Use `set i : Fin (k + 1) ⊕ Fin (k + 1) := Sum.inl (Fin.last k) with hi`. Use `set j : Fin (k + 1) ⊕ Fin (k + 1) := Sum.inr (Fin.last k) with hj`. Establish `hij : i ≠ j` using `by simp [hi, hj]`. Use `set D0 : Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) R := Matrix.fromBlocks Z 0 0 Y with hD0`. Use `set f : ((Fin (k + 1) ⊕ Fin (k + 1)) → R) → ((Fin (k + 1) ⊕ Fin (k + 1)) → R) → R := fun r1 r2 => ((D0.updateRow i r1).updateRow j r2).det with hf`.

Establish `hN : Matrix.fromBlocks Z (cornerM k s) (cornerM k t) Y = (D0.updateRow i (D0 i + s • Pi.single j 1)).updateRow j (D0 j + t • Pi.single i 1)`. Apply the tactic sequence `ext (a | a) (b | b) <;>`. Apply the tactic sequence `by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k <;>`. Simplify using `[hD0, hi, hj, cornerM, Matrix.updateRow_apply, Pi.single_apply, ha, hb]`. Establish `hlin2 : ∀ r1 u v : (Fin (k + 1) ⊕ Fin (k + 1)) → R, ∀ c : R, f r1 (u + c • v) = f r1 u + c * f r1 v`.

Introduce `r1 u v c`. Simplify using `only [hf, Matrix.det_updateRow_add, Matrix.det_updateRow_smul]`. Establish `hlin1 : ∀ r2 u v : (Fin (k + 1) ⊕ Fin (k + 1)) → R, ∀ c : R, f (u + c • v) r2 = f u r2 + c * f v r2`. Introduce `r2 u v c`. Simplify using `only [hf]`.

Rewrite using `[Matrix.updateRow_comm _ hij, Matrix.updateRow_comm _ hij, Matrix.updateRow_comm _ hij, Matrix.det_updateRow_add, Matrix.det_updateRow_smul]`. Establish `hdet : (Matrix.fromBlocks Z (cornerM k s) (cornerM k t) Y).det = f (D0 i + s • Pi.single j 1) (D0 j + t • Pi.single i 1)`. Rewrite using `[hN]`. Establish `h00 : f (D0 i) (D0 j) = Z.det * Y.det`. Simplify using `only [hf, Matrix.updateRow_eq_self, hD0, Matrix.det_fromBlocks_zero₂₁]`.

Establish `h10 : f (Pi.single j 1) (D0 j) = 0`. Simplify using `only [hf]`. Rewrite using `[Matrix.updateRow_comm _ hij, Matrix.updateRow_eq_self]`. Establish `: D0.updateRow i (Pi.single j 1) = Matrix.fromBlocks (Z.updateRow (Fin.last k) 0) (cornerM k 1) 0 Y`. Apply the tactic sequence `ext (a | a) (b | b) <;>`.

Apply the tactic sequence `by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k <;>`. Simplify using `[hD0, hi, hj, cornerM, Matrix.updateRow_apply, Pi.single_apply, ha, hb]`. Rewrite using `[this, Matrix.det_fromBlocks_zero₂₁, det_updateRow_last_zero, zero_mul]`. Establish `h01 : f (D0 i) (Pi.single i 1) = 0`. Simplify using `only [hf, Matrix.updateRow_eq_self]`.

Establish `: D0.updateRow j (Pi.single i 1) = Matrix.fromBlocks Z 0 (cornerM k 1) (Y.updateRow (Fin.last k) 0)`. Apply the tactic sequence `ext (a | a) (b | b) <;>`. Apply the tactic sequence `by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k <;>`. Simplify using `[hD0, hi, hj, cornerM, Matrix.updateRow_apply, Pi.single_apply, ha, hb]`. Rewrite using `[this, Matrix.det_fromBlocks_zero₁₂, det_updateRow_last_zero, mul_zero]`.

Establish `h11 : f (Pi.single j 1) (Pi.single i 1) = -((Z.submatrix Fin.castSucc Fin.castSucc).det * (Y.submatrix Fin.castSucc Fin.castSucc).det)`. Simplify using `only [hf]`. Establish `hsw : ((D0.updateRow i (Pi.single j 1)).updateRow j (Pi.single i 1)).submatrix (Equiv.swap i j) id = Matrix.fromBlocks (Z.updateRow (Fin.last k) (Pi.single (Fin.last k) 1)) 0 0 (Y.updateRow (Fin.last k) (Pi.single (Fin.last k) 1))`. Apply the tactic sequence `ext (a | a) (b | b) <;>`. Apply the tactic sequence `by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k <;>`.

Simplify using `[hD0, hi, hj, Matrix.updateRow_apply, Pi.single_apply, Equiv.swap_apply_def, ha, hb]`. Establish `h` using `Matrix.det_permute (Equiv.swap i j) ((D0.updateRow i (Pi.single j 1)).updateRow j (Pi.single i 1))`. Rewrite `h` using `[hsw, Matrix.det_fromBlocks_zero₂₁, det_updateRow_last_single, det_updateRow_last_single, Equiv.Perm.sign_swap hij]`. Rewrite using `[h]`. Simplify using the standard rewrite rules.

Rewrite using `[hdet, hlin2, hlin1, hlin1, h00, h10, h01, h11]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_N (Z Y : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (s t : R) :
    (Matrix.fromBlocks Z (cornerM k s) (cornerM k t) Y).det =
      Z.det * Y.det - s * t * ((Z.submatrix Fin.castSucc Fin.castSucc).det *
        (Y.submatrix Fin.castSucc Fin.castSucc).det) := by
  set i : Fin (k + 1) ⊕ Fin (k + 1) := Sum.inl (Fin.last k) with hi
  set j : Fin (k + 1) ⊕ Fin (k + 1) := Sum.inr (Fin.last k) with hj
  have hij : i ≠ j := by simp [hi, hj]
  set D0 : Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) R := Matrix.fromBlocks Z 0 0 Y with hD0
  set f : ((Fin (k + 1) ⊕ Fin (k + 1)) → R) → ((Fin (k + 1) ⊕ Fin (k + 1)) → R) → R :=
    fun r1 r2 => ((D0.updateRow i r1).updateRow j r2).det with hf
  have hN : Matrix.fromBlocks Z (cornerM k s) (cornerM k t) Y =
      (D0.updateRow i (D0 i + s • Pi.single j 1)).updateRow j (D0 j + t • Pi.single i 1) := by
    ext (a | a) (b | b) <;>
      by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k <;>
      simp [hD0, hi, hj, cornerM, Matrix.updateRow_apply, Pi.single_apply, ha, hb]

  have hlin2 : ∀ r1 u v : (Fin (k + 1) ⊕ Fin (k + 1)) → R, ∀ c : R,
      f r1 (u + c • v) = f r1 u + c * f r1 v := by
    intro r1 u v c
    simp only [hf, Matrix.det_updateRow_add, Matrix.det_updateRow_smul]

  have hlin1 : ∀ r2 u v : (Fin (k + 1) ⊕ Fin (k + 1)) → R, ∀ c : R,
      f (u + c • v) r2 = f u r2 + c * f v r2 := by
    intro r2 u v c
    simp only [hf]
    rw [Matrix.updateRow_comm _ hij, Matrix.updateRow_comm _ hij, Matrix.updateRow_comm _ hij,
      Matrix.det_updateRow_add, Matrix.det_updateRow_smul]
  have hdet : (Matrix.fromBlocks Z (cornerM k s) (cornerM k t) Y).det =
      f (D0 i + s • Pi.single j 1) (D0 j + t • Pi.single i 1) := by
    rw [hN]

  have h00 : f (D0 i) (D0 j) = Z.det * Y.det := by
    simp only [hf, Matrix.updateRow_eq_self, hD0, Matrix.det_fromBlocks_zero₂₁]
  have h10 : f (Pi.single j 1) (D0 j) = 0 := by
    simp only [hf]
    rw [Matrix.updateRow_comm _ hij, Matrix.updateRow_eq_self]
    have : D0.updateRow i (Pi.single j 1) =
        Matrix.fromBlocks (Z.updateRow (Fin.last k) 0) (cornerM k 1) 0 Y := by
      ext (a | a) (b | b) <;>
        by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k <;>
        simp [hD0, hi, hj, cornerM, Matrix.updateRow_apply, Pi.single_apply, ha, hb]
    rw [this, Matrix.det_fromBlocks_zero₂₁, det_updateRow_last_zero, zero_mul]
  have h01 : f (D0 i) (Pi.single i 1) = 0 := by
    simp only [hf, Matrix.updateRow_eq_self]
    have : D0.updateRow j (Pi.single i 1) =
        Matrix.fromBlocks Z 0 (cornerM k 1) (Y.updateRow (Fin.last k) 0) := by
      ext (a | a) (b | b) <;>
        by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k <;>
        simp [hD0, hi, hj, cornerM, Matrix.updateRow_apply, Pi.single_apply, ha, hb]
    rw [this, Matrix.det_fromBlocks_zero₁₂, det_updateRow_last_zero, mul_zero]
  have h11 : f (Pi.single j 1) (Pi.single i 1) =
      -((Z.submatrix Fin.castSucc Fin.castSucc).det * (Y.submatrix Fin.castSucc Fin.castSucc).det) := by
    simp only [hf]
    have hsw : ((D0.updateRow i (Pi.single j 1)).updateRow j (Pi.single i 1)).submatrix
        (Equiv.swap i j) id =
        Matrix.fromBlocks (Z.updateRow (Fin.last k) (Pi.single (Fin.last k) 1)) 0 0
          (Y.updateRow (Fin.last k) (Pi.single (Fin.last k) 1)) := by
      ext (a | a) (b | b) <;>
        by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k <;>
        simp [hD0, hi, hj, Matrix.updateRow_apply, Pi.single_apply, Equiv.swap_apply_def, ha, hb]
    have h := Matrix.det_permute (Equiv.swap i j) ((D0.updateRow i (Pi.single j 1)).updateRow j (Pi.single i 1))
    rw [hsw, Matrix.det_fromBlocks_zero₂₁, det_updateRow_last_single, det_updateRow_last_single,
      Equiv.Perm.sign_swap hij] at h
    rw [h]
    simp
  rw [hdet, hlin2, hlin1, hlin1, h00, h10, h01, h11]
  ring

end General

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Apply the tactic sequence `ext (a | a) (b | b) <;> simp [Ga, cornerM, Matrix.fromBlocks]`.
-/
theorem ga_eq_submatrix (D : Formalism.BasicNotions.D7) (T T' : D.host.E) (Z : MatZ D) :
    Ga T T' Z = (Matrix.fromBlocks Z (cornerM D.R.rS (-T)) (cornerM D.R.rS (-T')) Z.conjTranspose).submatrix id
      (Equiv.sumComm _ _) := by
  ext (a | a) (b | b) <;> simp [Ga, cornerM, Matrix.fromBlocks]

/- English proof (translation)
Unfold `leadMinorE`. Rewrite using `[dif_pos le_rfl]`. Use `congr 1`.
-/
theorem leadMinorE_full (D : Formalism.BasicNotions.D7) (Z : MatZ D) : leadMinorE Z (D.R.rS + 1) = Z.det := by
  unfold leadMinorE
  rw [dif_pos le_rfl]
  congr 1

/- English proof (translation)
Unfold `leadMinorE`. Rewrite using `[dif_pos (Nat.le_succ _)]`. Use `congr 1`.
-/
theorem leadMinorE_prev (D : Formalism.BasicNotions.D7) (Z : MatZ D) :
    leadMinorE Z D.R.rS = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  unfold leadMinorE
  rw [dif_pos (Nat.le_succ _)]
  congr 1

/- English proof (translation)
Rewrite using `[ga_eq_submatrix, Matrix.det_permute', det_N, GZ, leadMinorE_full, leadMinorE_prev, Matrix.det_conjTranspose, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_Ga (D : Formalism.BasicNotions.D7) (T T' : D.host.E) (Z : MatZ D) :
    (Ga T T' Z).det = ((Equiv.Perm.sign (Equiv.sumComm (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1))) : ℤ) : D.host.E) *
      GZ T T' Z := by
  rw [ga_eq_submatrix, Matrix.det_permute', det_N, GZ, leadMinorE_full, leadMinorE_prev,
    Matrix.det_conjTranspose, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]
  push_cast
  ring

end PI.UnitaryGroupMassFormula.CntFormula.DetGa

namespace PI.UnitaryGroupMassFormula.CntFormula

/- English proof (translation)
Introduce `D T T' Z hG`. Rewrite using `[DetGa.det_Ga]`. Use `mul_ne_zero ?_ hG` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.sumComm (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)))) with h | h <;>`. Apply the tactic sequence `rw [h] <;> simp`.
-/
theorem gram_determinant_ne_zero : DetGaNe := by
  intro D T T' Z hG
  rw [DetGa.det_Ga]
  refine mul_ne_zero ?_ hG
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.sumComm (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)))) with h | h <;>
    rw [h] <;> simp

end PI.UnitaryGroupMassFormula.CntFormula
