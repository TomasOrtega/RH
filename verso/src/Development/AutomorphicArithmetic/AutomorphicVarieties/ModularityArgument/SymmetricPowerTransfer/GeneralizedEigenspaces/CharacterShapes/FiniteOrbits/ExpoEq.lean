import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnitaryThreeTestFunctionHeckeRelations

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
The claim follows from `congrFun ((leviTorus k (Fin n)).symm_apply_apply t) i`.
-/
private theorem det_lt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (t : Fin n → kˣ) (i : Fin n) :
    Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) t i) = t i := congrFun ((leviTorus k (Fin n)).symm_apply_apply t) i

/- English proof (translation)
Establish `h0 : absPow k 0 = 1`. Use extensionality with `x`. Simplify using `[val_absPow]`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← absPow_add, show (1 : ℂ) + -1 = 0 by ring, h0]`.
-/
private theorem abs_one_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    absPow k 1 = (absPow k (-1))⁻¹ := by
  have h0 : absPow k 0 = 1 := by
    ext x
    simp [val_absPow]
  apply eq_inv_of_mul_eq_one_left
  rw [← absPow_add, show (1 : ℂ) + -1 = 0 by ring, h0]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[val_absPow]`.
-/
private theorem abs_zero_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    absPow k 0 = 1 := by
  ext x
  simp [val_absPow]

/- English proof (translation)
Introduce `k _ _ _ _ a`. Establish `hA : ∀ x : kˣ, absPow k 1 x = (absPow k (-1) x)⁻¹`. Introduce `x`. Rewrite using `[abs_one_eq]`. Both sides reduce to the same expression.

Establish `hZ : ∀ x : kˣ, absPow k 0 x = 1`. Introduce `x`. Rewrite using `[abs_zero_eq]`. Both sides reduce to the same expression. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `d`. Establish `m0 : modExp (fun _ : Fin 3 => Unit) 0 = 2` using `by decide`. Establish `m1 : modExp (fun _ : Fin 3 => Unit) 1 = 0` using `by decide`. Establish `m2 : modExp (fun _ : Fin 3 => Unit) 2 = -2` using `by decide`. Unfold `Dict.expo`.

Rewrite using `[← Units.val_mul]`. Use `congr 1`. Rewrite using `[torusChar_apply, MonoidHom.comp_apply, deltaHalf_apply, Fin.prod_univ_three, Fin.prod_univ_three]`. Simplify using `only [MulEquiv.coe_toMonoidHom, det_lt, m0, m1, m2]`. Establish `e0 : ((2 : ℤ) : ℂ) / 2 = 1` using `by norm_num`.

Establish `e1 : ((0 : ℤ) : ℂ) / 2 = 0` using `by norm_num`. Establish `e2 : ((-2 : ℤ) : ℂ) / 2 = -1` using `by norm_num`. Rewrite using `[e0, e1, e2, hA, hZ]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, MonoidHom.one_apply, MonoidHom.inv_apply, map_div]`. Use `ext`.

Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_div_eq_div_val, Units.val_one]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Introduce `t`. Establish `m0 : modExp (fun _ : Fin 2 => Unit) 0 = 1` using `by decide`.

Establish `m1 : modExp (fun _ : Fin 2 => Unit) 1 = -1` using `by decide`. Unfold `Dict.expo`. Rewrite using `[← Units.val_mul]`. Use `congr 1`. Rewrite using `[torusChar_apply, MonoidHom.comp_apply, deltaHalf_apply, Fin.prod_univ_two, Fin.prod_univ_two]`.

Simplify using `only [MulEquiv.coe_toMonoidHom, det_lt, m0, m1]`. Establish `hh : absPow k ((1 : ℤ) / 2) = absPow k 1 * absPow k ((-1 : ℤ) / 2)`. Rewrite using `[← absPow_add]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hh]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, MonoidHom.one_apply, MonoidHom.mul_apply, hA, map_inv]`. Use `ext`. Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]`.

Clear the denominators using the available nonvanishing facts. Introduce `n ψ`. Use `⟨fun d => Units.ne_zero _, ?_, ?_⟩` and prove the remaining obligations. Unfold `Dict.expo`. Simplify using the standard rewrite rules.

Introduce `d d'`. Unfold `Dict.expo`. Rewrite using `[← Units.val_mul]`. Use `congr 1`. Rewrite using `[map_mul, map_mul, mul_inv]`.

Use `ext`. Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val]`. Expand and normalize the polynomial expressions, which then agree.
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
