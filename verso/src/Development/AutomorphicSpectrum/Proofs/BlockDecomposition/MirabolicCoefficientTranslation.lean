import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

noncomputable section

namespace GlobalTheory.CompanionTheory.MirPair

section Alg

variable {k : Type} [Field k]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem uM_mul_uM (n : ℕ) (x y : Fin n → k) : uM n x * uM n y = uM n (x + y) := by
  unfold uM
  rw [← map_mul]
  rfl

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem det_glEmbMat (n : ℕ) (A : Matrix (Fin n) (Fin n) k) : (glEmbMat k n A).det = A.det := by
  have hrow : ∀ j : Fin n, GlobalTheory.BZMir.glEmbMat k n A (Fin.last n) (Fin.castSucc j) = 0 := by
    intro j
    simp [GlobalTheory.BZMir.glEmbMat]
  have hcorner : GlobalTheory.BZMir.glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by
    simp [GlobalTheory.BZMir.glEmbMat]
  have hminor : (GlobalTheory.BZMir.glEmbMat k n A).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = A := by
    ext i j
    simp [GlobalTheory.BZMir.glEmbMat, Fin.succAbove_last]
  have hsign : ((-1 : k) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]
    simp
  rw [Matrix.det_succ_row (GlobalTheory.BZMir.glEmbMat k n A) (Fin.last n), Fin.sum_univ_castSucc]
  simp only [hrow, hcorner, hminor, hsign, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, one_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem det_one_add_colMat (n : ℕ) (v : Fin n → k) : (1 + colMat k n v).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · apply Finset.prod_eq_one
    intro i _
    by_cases hi : i = Fin.last n
    · subst hi
      simp [GlobalTheory.BZMir.colMat]
    · simp [GlobalTheory.BZMir.colMat, hi]
  · intro i j hji
    change j < i at hji
    have hj : j ≠ Fin.last n := by
      intro h
      subst h
      exact absurd hji (not_lt.mpr (Fin.le_last i))
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hji)]
    simp [GlobalTheory.BZMir.colMat, hj]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem det_uM (n : ℕ) (y : Fin n → k) :
    GeneralLinearGroup.det ((uM n y : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  exact GlobalTheory.CompanionTheory.MirPair.det_one_add_colMat n y

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem det_levi (n : ℕ) (g : GL (Fin n) k) :
    GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = GeneralLinearGroup.det g := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact GlobalTheory.CompanionTheory.MirPair.det_glEmbMat n (g : Matrix (Fin n) (Fin n) k)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem uM_mul_levi (n : ℕ) (g : GL (Fin n) k) (x : Fin n → k) :
    uM n x * levi k n g =
      levi k n g * uM n (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x) := by
  have h := GlobalTheory.BZMir.glEmb_mul_unip' k n g
    (Multiplicative.ofAdd (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x))
  have hx : (g : Matrix (Fin n) (Fin n) k) *ᵥ (Multiplicative.toAdd
      (Multiplicative.ofAdd (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x))) = x := by
    rw [toAdd_ofAdd, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [hx] at h
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact h.symm

end Alg

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coef_rules (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V')
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ) (hB : TwInv T T' B s) :
    (∀ (y x : Fin (n + 1) → k) (v : V) (v' : V'), coef T B (T (uM (n + 1) y) v) v' x = coef T B v v' (x + y)) ∧
    (∀ (y x : Fin (n + 1) → k) (v : V) (v' : V'), coef T B v (T' (uM (n + 1) y) v') x = coef T B v v' (x - y)) ∧
    (∀ (g : GL (Fin (n + 1)) k) (x : Fin (n + 1) → k) (v : V) (v' : V'),
      coef T B (T (levi k (n + 1) g) v) (T' (levi k (n + 1) g) v') x =
        ((detChar (Fin (n + 1)) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) *
          coef T B v v' (((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x)) := by
  unfold GlobalTheory.CompanionTheory.MirPair.TwInv at hB
  have hT : ∀ (a b : GlobalTheory.BZMir.Mir k (n + 1)) (w : V), T a (T b w) = T (a * b) w := by
    intro a b w
    rw [map_mul, Module.End.mul_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro y x v v'
    simp only [GlobalTheory.CompanionTheory.MirPair.coef]
    rw [hT, GlobalTheory.CompanionTheory.MirPair.uM_mul_uM]
  · intro y x v v'
    simp only [GlobalTheory.CompanionTheory.MirPair.coef]
    have hxy : y + (x - y) = x := by abel
    have h := hB (GlobalTheory.CompanionTheory.MirPair.uM (n + 1) y) (T (GlobalTheory.CompanionTheory.MirPair.uM (n + 1) (x - y)) v) v'
    rw [GlobalTheory.SmGL.detChar_apply, GlobalTheory.CompanionTheory.MirPair.det_uM, map_one, Units.val_one, one_mul,
      hT, GlobalTheory.CompanionTheory.MirPair.uM_mul_uM, hxy] at h
    exact h
  · intro g x v v'
    simp only [GlobalTheory.CompanionTheory.MirPair.coef]
    rw [hT, GlobalTheory.CompanionTheory.MirPair.uM_mul_levi, ← hT, hB, GlobalTheory.SmGL.detChar_apply,
      GlobalTheory.SmGL.detChar_apply, GlobalTheory.CompanionTheory.MirPair.det_levi]

end Rep

end GlobalTheory.CompanionTheory.MirPair

end
