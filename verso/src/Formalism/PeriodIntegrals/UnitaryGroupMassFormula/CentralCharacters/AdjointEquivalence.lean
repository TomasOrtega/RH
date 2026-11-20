import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CentralCharacters.QdetMemAdjSub

noncomputable section

namespace PI.UnitaryGroupMassFormula.DSIC

open PI.DSInfCharCap
open scoped InnerProductSpace Matrix

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Separate the alternatives or extract the components of the hypothesis. Apply the first step, then apply the next step to every resulting obligation.

Simplify using the standard rewrite rules.
-/
theorem jm_sq {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  rcases eq_or_ne i j with rfl | h
  · cases hε : ε i <;> simp [Matrix.diagonal_apply, hε]
  · simp [Matrix.diagonal_apply, Matrix.one_apply, h]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem jm_jm_mul {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := by
  rw [← Matrix.mul_assoc, jm_sq, Matrix.one_mul]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jm_inv {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv (jm_sq ε)

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem jm_isUnit {n : ℕ} (ε : Fin n → Bool) : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, jm_sq ε, jm_sq ε⟩, rfl⟩

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_UJset_iff {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ PI.UpqRep.UJset ε ↔ gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := Iff.rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem exp_mem_UJ {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ PI.UpqRep.UJset ε := by
  rw [mem_UJset_iff]
  set A : Matrix (Fin n) (Fin n) ℂ := (t : ℂ) • X with hAdef
  have h0 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX
  have hX' : Xᴴ = -(Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) := by
    calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [Matrix.mul_assoc, jm_sq, Matrix.mul_one]
      _ = _ := by rw [h0, Matrix.neg_mul]
  have hA : Aᴴ = Formalism.REAL.Jm ε * (-A) * (Formalism.REAL.Jm ε)⁻¹ := by
    have ht : star (t : ℂ) = t := Complex.conj_ofReal t
    rw [jm_inv, hAdef, Matrix.conjTranspose_smul, hX', ht]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
  have hcomm : NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
    rw [← Matrix.exp_add_of_commute (-A) A (Commute.neg_left (Commute.refl A)), neg_add_cancel,
      NormedSpace.exp_zero]
  rw [← Matrix.exp_conjTranspose, hA, Matrix.exp_conj _ _ (jm_isUnit ε), jm_inv]
  calc Formalism.REAL.Jm ε * NormedSpace.exp (-A) * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε * NormedSpace.exp A
      = Formalism.REAL.Jm ε * (NormedSpace.exp (-A) * NormedSpace.exp A) := by
        simp only [Matrix.mul_assoc, jm_jm_mul]
    _ = Formalism.REAL.Jm ε := by rw [hcomm, Matrix.mul_one]

end PI.UnitaryGroupMassFormula.DSIC
