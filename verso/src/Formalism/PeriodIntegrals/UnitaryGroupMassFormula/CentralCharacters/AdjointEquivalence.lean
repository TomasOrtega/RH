import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CentralCharacters.QdetMemAdjSub

noncomputable section

namespace PI.UnitaryGroupMassFormula.DSIC

open PI.DSInfCharCap
open scoped InnerProductSpace Matrix

/- English proof (translation)
Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Use extensionality with `i j`. Break down `eq_or_ne i j with rfl | h` into its components or cases. Apply the tactic sequence `cases hε : ε i <;> simp [Matrix.diagonal_apply, hε]`.

Simplify using `[Matrix.diagonal_apply, Matrix.one_apply, h]`.
-/
theorem jm_sq {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  rcases eq_or_ne i j with rfl | h
  · cases hε : ε i <;> simp [Matrix.diagonal_apply, hε]
  · simp [Matrix.diagonal_apply, Matrix.one_apply, h]

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, jm_sq, Matrix.one_mul]`.
-/
theorem jm_jm_mul {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := by
  rw [← Matrix.mul_assoc, jm_sq, Matrix.one_mul]

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv (jm_sq ε)`.
-/
theorem jm_inv {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv (jm_sq ε)

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, jm_sq ε, jm_sq ε⟩, rfl⟩`.
-/
theorem jm_isUnit {n : ℕ} (ε : Fin n → Bool) : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, jm_sq ε, jm_sq ε⟩, rfl⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_UJset_iff {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ PI.UpqRep.UJset ε ↔ gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := Iff.rfl

/- English proof (translation)
Rewrite using `[mem_UJset_iff]`. Use `set A : Matrix (Fin n) (Fin n) ℂ := (t : ℂ) • X with hAdef`. Establish `h0 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X)` using `eq_neg_of_add_eq_zero_left hX`. Establish `hX' : Xᴴ = -(Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hA : Aᴴ = Formalism.REAL.Jm ε * (-A) * (Formalism.REAL.Jm ε)⁻¹`. Establish `ht : star (t : ℂ) = t` using `Complex.conj_ofReal t`. Rewrite using `[jm_inv, hAdef, Matrix.conjTranspose_smul, hX', ht]`. Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]`. Establish `hcomm : NormedSpace.exp (-A) * NormedSpace.exp A = 1`.

Rewrite using `[← Matrix.exp_add_of_commute (-A) A (Commute.neg_left (Commute.refl A)), neg_add_cancel, NormedSpace.exp_zero]`. Rewrite using `[← Matrix.exp_conjTranspose, hA, Matrix.exp_conj _ _ (jm_isUnit ε), jm_inv]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, jm_jm_mul]`. Use `_ = Formalism.REAL.Jm ε := by rw [hcomm, Matrix.mul_one]`.
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
