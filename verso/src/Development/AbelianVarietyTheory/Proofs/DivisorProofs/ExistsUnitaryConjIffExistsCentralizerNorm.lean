import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitaryConj

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem inv_h_form {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (h : GL (Fin n) K) :
    (h.val * cT σ h.val)⁻¹ = cT σ (h⁻¹).val * (h⁻¹).val := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (h⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul, cT_units]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Simplify to obtain the desired conclusion from the available facts.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem main : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (γ h : GL (Fin n) K), (∃ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) K), h⁻¹ * γ * h = g⁻¹ * γ * g) ↔ ∃ c : Matrix (Fin n) (Fin n) K, c * γ.val = γ.val * c ∧ cT σ c * c = (h.val * cT σ h.val)⁻¹ := by
  intro K _ σ n γ h
  rw [inv_h_form]
  constructor
  · rintro ⟨g, hg, hconj⟩
    have hg' : cT σ g.val * 1 * g.val = 1 := hg
    rw [Matrix.mul_one] at hg'
    refine ⟨(g * h⁻¹).val, ?_, ?_⟩
    · have e : g * h⁻¹ * γ = γ * (g * h⁻¹) := by
        calc g * h⁻¹ * γ = g * (h⁻¹ * γ * h) * h⁻¹ := by group
          _ = g * (g⁻¹ * γ * g) * h⁻¹ := by rw [hconj]
          _ = γ * (g * h⁻¹) := by group
      simpa only [Units.val_mul] using congrArg Units.val e
    · rw [Units.val_mul, cT_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ g.val), hg', Matrix.one_mul]
  · rintro ⟨c, hc, hcc⟩
    have hdet : c.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hcc
      rw [Matrix.det_mul, h0, mul_zero] at this
      have hne : (cT σ (h⁻¹).val * (h⁻¹).val).det ≠ 0 := det_ne σ h
      exact hne this.symm
    let cu : GL (Fin n) K := ((Matrix.isUnit_iff_isUnit_det c).mpr (isUnit_iff_ne_zero.mpr hdet)).unit
    have hcu : cu.val = c := rfl
    have hcom : cu⁻¹ * γ * cu = γ := by
      have e : cu * γ = γ * cu := Units.ext (by simpa only [Units.val_mul, hcu] using hc)
      calc cu⁻¹ * γ * cu = cu⁻¹ * (γ * cu) := by group
        _ = cu⁻¹ * (cu * γ) := by rw [e]
        _ = γ := by group
    refine ⟨cu * h, ?_, ?_⟩
    · show cT σ (cu * h).val * 1 * (cu * h).val = 1
      rw [Matrix.mul_one, Units.val_mul, cT_mul, hcu, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ c), hcc]
      simp only [Matrix.mul_assoc]
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one, ← cT_mul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, cT_one]
    · calc h⁻¹ * γ * h = h⁻¹ * (cu⁻¹ * γ * cu) * h := by rw [hcom]
        _ = (cu * h)⁻¹ * γ * (cu * h) := by group

end GlobalTheory.UnitaryConj
