import Formalism.ResultantValuation.SubspaceCount

noncomputable section

namespace Formalism.ResultantValuation

open Module

namespace ParabolicCounting

variable (F : Type) [Field F] (r t : ℕ)

def firstBlock : Submodule F (Fin (r + t) → F) where
  carrier := {v | ∀ i : Fin (r + t), r ≤ (i : ℕ) → v i = 0}
  add_mem' := by
    intro a b ha hb i hi
    simp [ha i hi, hb i hi]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c v hv i hi
    simp [hv i hi]

@[instance_reducible] def act : MulAction (GL (Fin (r + t)) F) (Submodule F (Fin (r + t) → F)) where
  smul g W := W.map (Matrix.mulVecLin (g : Matrix (Fin (r + t)) (Fin (r + t)) F))
  one_smul W := by
    show W.map _ = W
    rw [Units.val_one, Matrix.mulVecLin_one, Submodule.map_id]
  mul_smul g h W := by
    show W.map _ = (W.map _).map _
    rw [Units.val_mul, Matrix.mulVecLin_mul, Submodule.map_comp]

attribute [local instance] act

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smul_def (g : GL (Fin (r + t)) F) (W : Submodule F (Fin (r + t) → F)) :
    g • W = W.map (Matrix.mulVecLin (g : Matrix (Fin (r + t)) (Fin (r + t)) F)) := rfl

def lequiv (g : GL (Fin (r + t)) F) : (Fin (r + t) → F) ≃ₗ[F] (Fin (r + t) → F) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv F _ (Matrix.GeneralLinearGroup.toLin g)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem lequiv_coe (g : GL (Fin (r + t)) F) :
    ((lequiv F r t g : (Fin (r + t) → F) ≃ₗ[F] (Fin (r + t) → F)) :
        (Fin (r + t) → F) →ₗ[F] (Fin (r + t) → F)) =
      Matrix.mulVecLin (g : Matrix (Fin (r + t)) (Fin (r + t)) F) := by
  rw [lequiv, LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
    Matrix.GeneralLinearGroup.coe_toLin]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem finrank_smul (g : GL (Fin (r + t)) F) (W : Submodule F (Fin (r + t) → F)) :
    finrank F (g • W : Submodule F (Fin (r + t) → F)) = finrank F W := by
  rw [smul_def, ← lequiv_coe, LinearEquiv.finrank_map_eq]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mem_stabilizer_iff (g : GL (Fin (r + t)) F) :
    g ∈ MulAction.stabilizer (GL (Fin (r + t)) F) (firstBlock F r t) ↔
      g ∈ parabolicSet F r t := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h i j hi hj
    have hmem : (Pi.single j (1 : F) : Fin (r + t) → F) ∈ firstBlock F r t := by
      intro k hk
      have hkj : k ≠ j := by
        intro e
        subst e
        omega
      simp [hkj]
    have h2 : Matrix.mulVecLin (g : Matrix (Fin (r + t)) (Fin (r + t)) F) (Pi.single j 1) ∈
        firstBlock F r t := by
      rw [← h, smul_def]
      exact Submodule.mem_map_of_mem hmem
    have h3 := h2 i hi
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using h3
  · intro hg
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [smul_def]
      rintro _ ⟨v, hv, rfl⟩ i hi
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : (j : ℕ) < r
      · simp [hg i j hi hj]
      · simp [hv j (by omega)]
    · exact finrank_smul F r t g _

end ParabolicCounting

end Formalism.ResultantValuation
