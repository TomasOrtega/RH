import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

open TensorProduct

/- English proof (translation)
Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul c v`. Proceed by induction on `v using Finsupp.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [tmul_add, map_add, ha, hb]`. Consider the case `single x n`. Establish `e1 : TensorProduct.finsuppScalarRight ℤ ℤ ℂ X (c ⊗ₜ[ℤ] Finsupp.single x n) = ((n : ℂ) * c) • Finsupp.single x (1 : ℂ)`. Use extensionality with `x'`.

Rewrite using `[TensorProduct.finsuppScalarRight_apply_tmul_apply]`. Distinguish the cases in `hx : x = x'`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Finsupp.single_apply, hx]`.

Establish `e2 : Finsupp.single x n = n • Finsupp.single x (1 : ℤ)` using `by simp`. Use extensionality with `y`. Rewrite using `[e1, map_smul, LinearMap.lTensor_tmul, TensorProduct.finsuppScalarRight_apply_tmul_apply, e2, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, h]`. Simplify using `only [smul_eq_mul, zsmul_eq_mul, Int.cast_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ladder {X Y : Type} [DecidableEq X] [DecidableEq Y] (f : (X →₀ ℤ) →ₗ[ℤ] (Y →₀ ℤ)) (f' : (X →₀ ℂ) →ₗ[ℂ] (Y →₀ ℂ))
    (h : ∀ x y, f' (Finsupp.single x 1) y = (f (Finsupp.single x 1) y : ℤ)) (u : ℂ ⊗[ℤ] (X →₀ ℤ)) :
    f' (TensorProduct.finsuppScalarRight ℤ ℤ ℂ X u) = TensorProduct.finsuppScalarRight ℤ ℤ ℂ Y (f.lTensor ℂ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul c v =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
    | single x n =>
      have e1 : TensorProduct.finsuppScalarRight ℤ ℤ ℂ X (c ⊗ₜ[ℤ] Finsupp.single x n)
          = ((n : ℂ) * c) • Finsupp.single x (1 : ℂ) := by
        ext x'
        rw [TensorProduct.finsuppScalarRight_apply_tmul_apply]
        by_cases hx : x = x'
        · subst hx; simp
        · simp [Finsupp.single_apply, hx]
      have e2 : Finsupp.single x n = n • Finsupp.single x (1 : ℤ) := by simp
      ext y
      rw [e1, map_smul, LinearMap.lTensor_tmul, TensorProduct.finsuppScalarRight_apply_tmul_apply, e2, map_smul,
        Finsupp.smul_apply, Finsupp.smul_apply, h]
      simp only [smul_eq_mul, zsmul_eq_mul, Int.cast_mul]
      push_cast
      ring

/- English proof (translation)
Introduce `X Y Z f g f' g' hf hg hfg`. Establish `hex` using `Module.Flat.lTensor_exact ℂ hfg`. Use `Function.Exact.of_ladder_addEquiv_of_exact (TensorProduct.finsuppScalarRight ℤ ℤ ℂ X).toAddEquiv (TensorProduct.finsuppScalarRight ℤ ℤ ℂ Y).toAddEquiv (TensorProduct.finsuppScalarRight ℤ ℤ ℂ Z).toAddEquiv (f₁₂ := (f.lTensor ℂ).toAddMonoidHom) (f₂₃ := (g.lTensor ℂ).toAddMonoidHom) …` and prove the remaining obligations. Conclude with `AddMonoidHom.ext fun u => ladder f f' hf u`. Conclude with `AddMonoidHom.ext fun u => ladder g g' hg u`.
-/
theorem UpperTheory.exactBase_integral_to_complex :
    UpperTheory.V.Af.BA.ExactBase := by
  intro X Y Z f g f' g' hf hg hfg
  classical
  have hex := Module.Flat.lTensor_exact ℂ hfg
  refine Function.Exact.of_ladder_addEquiv_of_exact
    (TensorProduct.finsuppScalarRight ℤ ℤ ℂ X).toAddEquiv
    (TensorProduct.finsuppScalarRight ℤ ℤ ℂ Y).toAddEquiv
    (TensorProduct.finsuppScalarRight ℤ ℤ ℂ Z).toAddEquiv
    (f₁₂ := (f.lTensor ℂ).toAddMonoidHom) (f₂₃ := (g.lTensor ℂ).toAddMonoidHom)
    (g₁₂ := f'.toAddMonoidHom) (g₂₃ := g'.toAddMonoidHom) ?_ ?_ hex
  · exact AddMonoidHom.ext fun u => ladder f f' hf u
  · exact AddMonoidHom.ext fun u => ladder g g' hg u
