import Mathlib
open TensorProduct Module

/- English proof (translation)
Introduce `F _ B _ _ V _ _ n _ _ b`. Set `e : V ⊗[F] B ≃ₗ[F] (n → B)` to `(TensorProduct.comm F V B) ≪≫ₗ (TensorProduct.congr (LinearEquiv.refl F B) b.equivFun) ≪≫ₗ TensorProduct.piScalarRight F F B n`. Establish `h1 : ∀ v x i, e (v ⊗ₜ[F] x) i = b.repr v i • x`. Introduce `v x i`. Simplify using `[e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]`.

Establish `hadd : ∀ y z : V ⊗[F] B, e (y + z) = e y + e z` using `fun y z => map_add e y z`. Use `⟨e, h1, ?_, ?_⟩` and prove the remaining obligations. Introduce `y`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Use function extensionality and compare the values at `j`.

Rewrite using `[map_sum, Finset.sum_apply]`. Simplify using `only [h1, Basis.repr_self, Finsupp.single_apply]`. Simplify using the standard rewrite rules. Introduce `r f y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero`. Simplify using `only [map_zero]`. Rewrite using `[show (fun _ : n => f ((0 : n → B) _)) = 0 from by funext i; simp, Matrix.mulVec_zero]`. Consider the case `tmul v x`. Use function extensionality and compare the values at `i`.

Rewrite using `[TensorProduct.map_tmul, h1]`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, LinearMap.toMatrix_apply, h1, map_smul]`. Repeatedly rewrite using `[← Algebra.smul_def, smul_smul]`. Rewrite using `[← Finset.sum_smul]`. Use `congr 1`.

Use `conv_lhs => rw [← b.sum_repr v]`. Rewrite using `[map_sum, map_sum, Finsupp.finset_sum_apply]`. Simplify using `only [map_smul, Finsupp.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Consider the case `add y z hy hz`.

Rewrite using `[map_add, hadd, hy, hz, hadd, ← Matrix.mulVec_add]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[map_add]`.
-/
theorem GlobalTheory.tensorBasisCoords : ∀ (F : Type) [Field F] (B : Type) [CommRing B] [Algebra F B] (V : Type) [AddCommGroup V] [Module F V] (n : Type) [Fintype n] [DecidableEq n] (b : Basis n F V), ∃ e : V ⊗[F] B ≃ₗ[F] (n → B), (∀ v x i, e (v ⊗ₜ[F] x) i = b.repr v i • x) ∧ (∀ y : n → B, e.symm y = ∑ i, b i ⊗ₜ[F] y i) ∧ ∀ (r : V →ₗ[F] V) (f : B →ₗ[F] B) (y : V ⊗[F] B), e (TensorProduct.map r f y) = ((LinearMap.toMatrix b b r).map (algebraMap F B)).mulVec (fun i => f (e y i)) := by
  intro F _ B _ _ V _ _ n _ _ b
  let e : V ⊗[F] B ≃ₗ[F] (n → B) :=
    (TensorProduct.comm F V B) ≪≫ₗ (TensorProduct.congr (LinearEquiv.refl F B) b.equivFun) ≪≫ₗ
      TensorProduct.piScalarRight F F B n
  have h1 : ∀ v x i, e (v ⊗ₜ[F] x) i = b.repr v i • x := by
    intro v x i
    simp [e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  have hadd : ∀ y z : V ⊗[F] B, e (y + z) = e y + e z := fun y z => map_add e y z
  refine ⟨e, h1, ?_, ?_⟩
  · intro y
    rw [LinearEquiv.symm_apply_eq]
    funext j
    rw [map_sum, Finset.sum_apply]
    simp only [h1, Basis.repr_self, Finsupp.single_apply]
    simp
  · intro r f y
    induction y using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
      rw [show (fun _ : n => f ((0 : n → B) _)) = 0 from by funext i; simp, Matrix.mulVec_zero]
    | tmul v x =>
      funext i
      rw [TensorProduct.map_tmul, h1]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, LinearMap.toMatrix_apply, h1, map_smul]
      simp_rw [← Algebra.smul_def, smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      conv_lhs => rw [← b.sum_repr v]
      rw [map_sum, map_sum, Finsupp.finset_sum_apply]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    | add y z hy hz =>
      rw [map_add, hadd, hy, hz, hadd, ← Matrix.mulVec_add]
      congr 1
      funext i
      simp [map_add]
