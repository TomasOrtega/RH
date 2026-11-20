import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitaryConj

/- English proof (translation)
Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (h⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, cT_units]`.
-/
theorem inv_h_form {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (h : GL (Fin n) K) :
    (h.val * cT σ h.val)⁻¹ = cT σ (h⁻¹).val * (h⁻¹).val := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (h⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul, cT_units]

/- English proof (translation)
Introduce `K _ σ n γ h`. Rewrite using `[inv_h_form]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, hconj⟩`. Establish `hg' : cT σ g.val * 1 * g.val = 1` using `hg`.

Rewrite `hg'` using `[Matrix.mul_one]`. Use `⟨(g * h⁻¹).val, ?_, ?_⟩` and prove the remaining obligations. Establish `e : g * h⁻¹ * γ = γ * (g * h⁻¹)`. Combine the equalities or inequalities in the displayed calculation. Simplify `congrArg Units.val e` using `only [Units.val_mul]`.

Rewrite using `[Units.val_mul, cT_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ g.val), hg', Matrix.one_mul]`. Introduce and unpack `⟨c, hc, hcc⟩`. Establish `hdet : c.det ≠ 0`. Introduce `h0`. Use `congrArg Matrix.det hcc` as an intermediate fact.

Rewrite `this` using `[Matrix.det_mul, h0, mul_zero]`. Establish `hne : (cT σ (h⁻¹).val * (h⁻¹).val).det ≠ 0` using `det_ne σ h`. Conclude with `hne this.symm`. Set `cu : GL (Fin n) K` to `((Matrix.isUnit_iff_isUnit_det c).mpr (isUnit_iff_ne_zero.mpr hdet)).unit`. Establish `hcu : cu.val = c` using `rfl`.

Establish `hcom : cu⁻¹ * γ * cu = γ`. Establish `e : cu * γ = γ * cu` using `Units.ext (by simpa only [Units.val_mul, hcu] using hc)`. Combine the equalities or inequalities in the displayed calculation. Use `⟨cu * h, ?_, ?_⟩` and prove the remaining obligations. Use `show cT σ (cu * h).val * 1 * (cu * h).val = 1`.

Rewrite using `[Matrix.mul_one, Units.val_mul, cT_mul, hcu, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ c), hcc]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one, ← cT_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, cT_one]`. Combine the equalities or inequalities in the displayed calculation.
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
