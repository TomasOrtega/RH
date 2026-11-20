import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.Common

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

variable {R : Type} [CommRing R] {r : ℕ}

def cornerM (r : ℕ) (c : R) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then c else 0

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem cornerM_castSucc_left (c : R) (a : Fin r) (b : Fin (r + 1)) :
    cornerM r c a.castSucc b = 0 := by
  simp [cornerM, (Fin.castSucc_lt_last a).ne]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem cornerM_castSucc_right (c : R) (a : Fin (r + 1)) (b : Fin r) :
    cornerM r c a b.castSucc = 0 := by
  simp [cornerM, (Fin.castSucc_lt_last b).ne]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem cornerM_last (c : R) : cornerM r c (Fin.last r) (Fin.last r) = c := by
  simp [cornerM]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem cornerM_map {S : Type} [CommRing S] (f : R →+* S) (c : R) :
    (cornerM r c).map f = cornerM r (f c) := by
  ext a b
  simp only [cornerM, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem head_add_cornerM (A : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (c : R) :
    (A + cornerM r c).submatrix Fin.castSucc Fin.castSucc = A.submatrix Fin.castSucc Fin.castSucc := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.add_apply, cornerM_castSucc_left, add_zero]

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem det_updateRow_last_single (A : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).det =
      (A.submatrix Fin.castSucc Fin.castSucc).det := by
  have hsub : (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix Fin.castSucc
      Fin.castSucc = A.submatrix Fin.castSucc Fin.castSucc := by
    ext a b
    simp [Matrix.updateRow_ne (Fin.castSucc_lt_last a).ne]
  rw [Matrix.det_succ_row _ (Fin.last r), Finset.sum_eq_single (Fin.last r)]
  · rw [Fin.succAbove_last, hsub, Matrix.updateRow_self, Pi.single_eq_same, mul_one,
      Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  · intro j _ hj
    rw [Matrix.updateRow_self, Pi.single_eq_of_ne hj, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Substitute using the available equality. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem det_add_cornerM (A : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (c : R) :
    (A + cornerM r c).det = A.det + c * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  have h : A + cornerM r c =
      A.updateRow (Fin.last r) (A (Fin.last r) + c • Pi.single (Fin.last r) 1) := by
    ext i j
    by_cases hi : i = Fin.last r
    · subst hi
      by_cases hj : j = Fin.last r
      · subst hj
        simp [cornerM]
      · simp [cornerM, hj, Pi.single_apply]
    · simp [cornerM, hi, Matrix.updateRow_ne hi]
  rw [h, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
    det_updateRow_last_single]

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem headCols_add_cornerM (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (c : R) :
    headCols (Z + cornerM r c) = headCols Z := by
  unfold headCols
  simp only [Matrix.add_apply, cornerM_castSucc_right, add_zero]

def mbeShift (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (c : R) : MbMod (Z + cornerM r c) ≃ₗ[R] MbMod Z :=
  Submodule.quotEquivOfEq _ _ (headCols_add_cornerM Z c)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mbeShift_mk (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (c : R) (v : Fin (r + 1) → R) :
    mbeShift Z c (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mbeShift_eCl (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (c : R) :
    mbeShift Z c (eCl (Z + cornerM r c)) = eCl Z := rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem mbeShift_bCls (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (c : R) :
    mbeShift Z c (bCls (Z + cornerM r c)) = bCls Z + c • eCl Z := by
  unfold bCls eCl
  rw [mbeShift_mk, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1
  funext i
  by_cases hi : i = Fin.last r
  · subst hi
    simp [cornerM]
  · simp [cornerM, hi, Pi.single_apply]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem card_isoMbe_shift (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (c : R) :
    Nat.card (IsoMbe (Z₁ + cornerM r c) (Z₂ + cornerM r c)) = Nat.card (IsoMbe Z₁ Z₂) := by
  have he₁ := mbeShift_eCl Z₁ c
  have he₂ := mbeShift_eCl Z₂ c
  have hb₁ := mbeShift_bCls Z₁ c
  have hb₂ := mbeShift_bCls Z₂ c
  refine Nat.card_congr
    { toFun := fun γ => ⟨((mbeShift Z₁ c).symm.trans γ.1).trans (mbeShift Z₂ c), ?_, ?_⟩
      invFun := fun δ => ⟨((mbeShift Z₁ c).trans δ.1).trans (mbeShift Z₂ c).symm, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have k : (mbeShift Z₁ c).symm (bCls Z₁) =
        bCls (Z₁ + cornerM r c) - c • eCl (Z₁ + cornerM r c) := by
      rw [LinearEquiv.symm_apply_eq, map_sub, map_smul, hb₁, he₁, add_sub_cancel_right]
    simp only [LinearEquiv.trans_apply, k, map_sub, map_smul, γ.2.1, γ.2.2, hb₂, he₂,
      add_sub_cancel_right]
  · have k : (mbeShift Z₁ c).symm (eCl Z₁) = eCl (Z₁ + cornerM r c) := by
      rw [LinearEquiv.symm_apply_eq, he₁]
    simp only [LinearEquiv.trans_apply, k, γ.2.2, he₂]
  · simp only [LinearEquiv.trans_apply, hb₁, map_add, map_smul, δ.2.1, δ.2.2]
    rw [← map_smul, ← map_add, LinearEquiv.symm_apply_eq, hb₂]
  · simp only [LinearEquiv.trans_apply, he₁, δ.2.2]
    rw [LinearEquiv.symm_apply_eq, he₂]
  · intro γ
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simp
  · intro δ
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simp

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
