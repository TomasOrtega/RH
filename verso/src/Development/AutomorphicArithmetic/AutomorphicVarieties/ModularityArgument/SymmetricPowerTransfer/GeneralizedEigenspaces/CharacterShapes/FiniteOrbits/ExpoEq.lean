import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnitaryThreeTestFunctionHeckeRelations

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem det_lt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (t : Fin n → kˣ) (i : Fin n) :
    Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) t i) = t i := congrFun ((leviTorus k (Fin n)).symm_apply_apply t) i

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
private theorem abs_one_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    absPow k 1 = (absPow k (-1))⁻¹ := by
  have h0 : absPow k 0 = 1 := by
    ext x
    simp [val_absPow]
  apply eq_inv_of_mul_eq_one_left
  rw [← absPow_add, show (1 : ℂ) + -1 = 0 by ring, h0]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
private theorem abs_zero_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    absPow k 0 = 1 := by
  ext x
  simp [val_absPow]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Z.Sym.So.expoEq :
    UpperTheory.V.Z.Sym.So.ExpoEq := by
  intro k _ _ _ _ a
  have hA : ∀ x : kˣ, absPow k 1 x = (absPow k (-1) x)⁻¹ := by
    intro x
    rw [abs_one_eq]
    rfl
  have hZ : ∀ x : kˣ, absPow k 0 x = 1 := by
    intro x
    rw [abs_zero_eq]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro d
    have m0 : modExp (fun _ : Fin 3 => Unit) 0 = 2 := by decide
    have m1 : modExp (fun _ : Fin 3 => Unit) 1 = 0 := by decide
    have m2 : modExp (fun _ : Fin 3 => Unit) 2 = -2 := by decide
    unfold Dict.expo
    rw [← Units.val_mul]
    congr 1
    rw [torusChar_apply, MonoidHom.comp_apply, deltaHalf_apply, Fin.prod_univ_three, Fin.prod_univ_three]
    simp only [MulEquiv.coe_toMonoidHom, det_lt, m0, m1, m2]
    have e0 : ((2 : ℤ) : ℂ) / 2 = 1 := by norm_num
    have e1 : ((0 : ℤ) : ℂ) / 2 = 0 := by norm_num
    have e2 : ((-2 : ℤ) : ℂ) / 2 = -1 := by norm_num
    rw [e0, e1, e2, hA, hZ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, MonoidHom.one_apply, MonoidHom.inv_apply, map_div]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_div_eq_div_val, Units.val_one]
    simp
    ring
  · intro t
    have m0 : modExp (fun _ : Fin 2 => Unit) 0 = 1 := by decide
    have m1 : modExp (fun _ : Fin 2 => Unit) 1 = -1 := by decide
    unfold Dict.expo
    rw [← Units.val_mul]
    congr 1
    rw [torusChar_apply, MonoidHom.comp_apply, deltaHalf_apply, Fin.prod_univ_two, Fin.prod_univ_two]
    simp only [MulEquiv.coe_toMonoidHom, det_lt, m0, m1]
    have hh : absPow k ((1 : ℤ) / 2) = absPow k 1 * absPow k ((-1 : ℤ) / 2) := by
      rw [← absPow_add]
      congr 1
      push_cast
      ring
    rw [hh]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      MonoidHom.one_apply, MonoidHom.mul_apply, hA, map_inv]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]
    field_simp
  · intro n ψ
    refine ⟨fun d => Units.ne_zero _, ?_, ?_⟩
    · unfold Dict.expo
      simp
    · intro d d'
      unfold Dict.expo
      rw [← Units.val_mul]
      congr 1
      rw [map_mul, map_mul, mul_inv]
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      ring

end
