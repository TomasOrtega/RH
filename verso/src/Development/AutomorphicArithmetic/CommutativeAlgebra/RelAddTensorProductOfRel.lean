import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsEtaleTrivializationOfTwoInvertibleModuleTo

open CategoryTheory TensorProduct UpperTheory.PicD

/- English proof (translation)
Set `e` to `LinearEquiv.ofBijective _ h`. Set `e'` to `LinearEquiv.ofBijective _ h'`. Set `F : C ⊗[A] (M ⊗[A] M') ≃ₗ[C] C` to `TensorProduct.AlgebraTensorModule.distribBaseChange A C M M' ≪≫ₗ TensorProduct.congr e e' ≪≫ₗ TensorProduct.lid C C`. Establish `hF : ∀ x, F x = LinearMap.liftBaseChange C ((Algebra.TensorProduct.lmul' A (S` using `C)).toLinearMap ∘ₗ TensorProduct.map t t') x := by`. Introduce `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Consider the case `tmul c y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add y1 y2 h1 h2 => rw [TensorProduct.tmul_add, map_add, map_add, h1, h2]`. Consider the case `tmul m m'`. Simplify using `[F, e, e', LinearMap.liftBaseChange_tmul, smul_eq_mul, mul_assoc]`. Establish `: ⇑(LinearMap.liftBaseChange C ((Algebra.TensorProduct.lmul' A (S` using `C)).toLinearMap ∘ₗ TensorProduct.map t t')) = F := by`.

Use function extensionality and compare the values at `x`. Conclude with `(hF x).symm`. Rewrite using `[this]`. Conclude with `F.bijective`.
-/
private theorem cotangentAtUnit_tangentBijection {A C M M' : Type} [CommRing A] [CommRing C] [Algebra A C]
    [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (t : M →ₗ[A] C) (t' : M' →ₗ[A] C)
    (h : Function.Bijective (LinearMap.liftBaseChange C t))
    (h' : Function.Bijective (LinearMap.liftBaseChange C t')) :
    Function.Bijective (LinearMap.liftBaseChange C
      ((Algebra.TensorProduct.lmul' A (S := C)).toLinearMap ∘ₗ TensorProduct.map t t')) := by
  let e := LinearEquiv.ofBijective _ h
  let e' := LinearEquiv.ofBijective _ h'
  let F : C ⊗[A] (M ⊗[A] M') ≃ₗ[C] C :=
    TensorProduct.AlgebraTensorModule.distribBaseChange A C M M' ≪≫ₗ TensorProduct.congr e e' ≪≫ₗ
      TensorProduct.lid C C
  have hF : ∀ x, F x = LinearMap.liftBaseChange C
      ((Algebra.TensorProduct.lmul' A (S := C)).toLinearMap ∘ₗ TensorProduct.map t t') x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y1 y2 h1 h2 => rw [TensorProduct.tmul_add, map_add, map_add, h1, h2]
      | tmul m m' =>
        simp [F, e, e', LinearMap.liftBaseChange_tmul, smul_eq_mul, mul_assoc]
  have : ⇑(LinearMap.liftBaseChange C
      ((Algebra.TensorProduct.lmul' A (S := C)).toLinearMap ∘ₗ TensorProduct.map t t')) = F := by
    funext x
    exact (hF x).symm
  rw [this]
  exact F.bijective

/- English proof (translation)
Introduce `P A _ z z' M M' _ _ _ _ hz hz'`. Take `⟨C, i1, i2, hff, het, w, g, t, w', g', t', T, T'⟩` from `UpperTheory.exists_etale_trivialization_of_two_invertibleModuleTorsors P A z z' M M' hz hz'`. Use `⟨C, i1, i2, hff, het, w + w', g * g', (Algebra.TensorProduct.lmul' A (S := C)).toLinearMap ∘ₗ TensorProduct.map t t', ?_⟩` and prove the remaining obligations. Use `⟨?_, ?_, ?_, cotangentAtUnit_tangentBijection t t' T.bij T'.bij⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add, T.dw, T'.dw]`.

Rewrite using `[P.un_mul, T.hg, T'.hg, map_add, map_add]`. Normalize the expressions using the abelian group laws. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => rw [map_add, add_smul, hx, hy, TensorProduct.tmul_add]`. Consider the case `tmul m m'`. Establish `h1` using `T.ht m`. Establish `h2` using `T'.ht m'`. Simplify using `only [LinearMap.comp_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, Algebra.TensorProduct.lmul'_apply_tmul, Units.val_mul]`.

Rewrite `h1`, `h2`, the goal using `[Algebra.smul_def]`. Rewrite using `[map_mul, show ∀ a b c d : C ⊗[A] C, a * b * (c * d) = (a * c) * (b * d) from fun a b c d => by ring, h1, h2, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`.
-/
theorem UpperTheory.rel_add_tensorProduct_of_rel :
    ∀ (P : Data) (A : Type) [CommRing A] (z z' : P.S1.obj (CommRingCat.of A)) (M M' : Type) [AddCommGroup M] [Module A M]
        [AddCommGroup M'] [Module A M'], P.Rel z M → P.Rel z' M' → P.Rel (z + z') (M ⊗[A] M') := by
  intro P A _ z z' M M' _ _ _ _ hz hz'
  obtain ⟨C, i1, i2, hff, het, w, g, t, w', g', t', T, T'⟩ := UpperTheory.exists_etale_trivialization_of_two_invertibleModuleTorsors P A z z' M M' hz hz'
  refine ⟨C, i1, i2, hff, het, w + w', g * g',
    (Algebra.TensorProduct.lmul' A (S := C)).toLinearMap ∘ₗ TensorProduct.map t t', ?_⟩
  refine ⟨?_, ?_, ?_, cotangentAtUnit_tangentBijection t t' T.bij T'.bij⟩
  · rw [map_add, map_add, T.dw, T'.dw]
  · rw [P.un_mul, T.hg, T'.hg, map_add, map_add]
    abel
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, add_smul, hx, hy, TensorProduct.tmul_add]
    | tmul m m' =>
      have h1 := T.ht m
      have h2 := T'.ht m'
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        Algebra.TensorProduct.lmul'_apply_tmul, Units.val_mul]
      rw [Algebra.smul_def] at h1 h2 ⊢
      rw [map_mul, show ∀ a b c d : C ⊗[A] C, a * b * (c * d) = (a * c) * (b * d) from
        fun a b c d => by ring, h1, h2, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
