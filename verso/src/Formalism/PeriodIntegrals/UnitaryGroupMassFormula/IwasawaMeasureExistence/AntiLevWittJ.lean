import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.MemLeviGLOf

noncomputable section

namespace PI.IwaMeasEx.PD

open Matrix NumberField Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs Formalism.L2.S.S7.WittLeviSubgroups
open scoped TensorProduct

section Witt

variable {J n₀ : ℕ} (c : Composition J)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem antiLev_wittJ {R : Type} [CommRing R] [StarRing R] (J0 : Matrix (Fin n₀) (Fin n₀) R) :
    AntiLev (levW (n₀ := n₀) c) c.length (wittJ (J := J) J0) := by
  intro q r h
  have hs : ∀ s : Fin J, (c.index s : ℕ) < c.length := fun s => (c.index s).isLt
  rcases q with q | q | q <;> rcases r with r | r | r <;>
    simp [wittJ, levW, Matrix.one_apply] at h ⊢
  all_goals first
    | (obtain ⟨rfl, -⟩ := h; have := hs q; omega)
    | omega

end Witt

section Frame

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J)

abbrev eW : WIdx J (nz I J) ≃ Fin I.n := widx I Fr.hJ

abbrev Bm : Matrix (Fin I.n) (Fin I.n) I.E := (Fr.B : Matrix (Fin I.n) (Fin I.n) I.E)

abbrev Bi : Matrix (Fin I.n) (Fin I.n) I.E := ((Fr.B⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem Bm_Bi : Bm Fr * Bi Fr = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem Bi_Bm : Bi Fr * Bm Fr = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

def wcE (h : Matrix (Fin I.n) (Fin I.n) I.E) : Matrix (WIdx J (nz I J)) (WIdx J (nz I J)) I.E :=
  (Bi Fr * h * Bm Fr).submatrix (eW Fr) (eW Fr)

def unwc (A : Matrix (WIdx J (nz I J)) (WIdx J (nz I J)) I.E) : Matrix (Fin I.n) (Fin I.n) I.E :=
  Bm Fr * A.submatrix (eW Fr).symm (eW Fr).symm * Bi Fr

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem unwc_mul (A B : Matrix (WIdx J (nz I J)) (WIdx J (nz I J)) I.E) :
    unwc Fr A * unwc Fr B = unwc Fr (A * B) := by
  unfold unwc
  rw [← submatrix_mul_equiv A B (eW Fr).symm (eW Fr).symm (eW Fr).symm]
  calc Bm Fr * A.submatrix (eW Fr).symm (eW Fr).symm * Bi Fr * (Bm Fr * B.submatrix (eW Fr).symm (eW Fr).symm * Bi Fr)
      = Bm Fr * A.submatrix (eW Fr).symm (eW Fr).symm * (Bi Fr * Bm Fr) * B.submatrix (eW Fr).symm (eW Fr).symm * Bi Fr := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [Bi_Bm, Matrix.mul_one]; simp only [Matrix.mul_assoc]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem unwc_one : unwc Fr 1 = 1 := by
  unfold unwc
  rw [submatrix_one_equiv, Matrix.mul_one, Bm_Bi]

/- English proof (translation)
By extensionality, compare the relevant components. Both sides reduce to the same expression.
-/
theorem cT_eq (M : Matrix (Fin I.n) (Fin I.n) I.E) : Formalism.UG.cT (starRingEnd I.E) M = Mᴴ := by
  ext i j; rfl

abbrev Gm : Matrix (Fin I.n) (Fin I.n) I.E := (Bm Fr)ᴴ * I.J * Bm Fr

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem Gm_sub : (Gm Fr).submatrix (eW Fr) (eW Fr) = wittJ (J := J) Fr.J0 := by
  ext r s
  have := Fr.gram r s
  rw [cT_eq] at this
  exact this

end Frame

section Flag

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J) (c : Composition J)

end Flag

end PI.IwaMeasEx.PD

end
