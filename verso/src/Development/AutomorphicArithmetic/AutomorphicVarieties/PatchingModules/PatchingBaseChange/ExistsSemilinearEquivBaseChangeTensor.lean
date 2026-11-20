import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

/- English proof (translation)
Introduce `B P B' P₁ P' _ _ _ _ _ _ _ _ _ τ M M' _ _ _ _ μ h`. Use `letI : Algebra P₁ P' := τ.toRingHom.toAlgebra`. Use `letI : Algebra P P' := (τ.toRingHom.comp (algebraMap P P₁)).toAlgebra`. Use `letI : Algebra B P' := ((algebraMap B' P').comp (algebraMap B B')).toAlgebra`. Use `haveI : IsScalarTower P P₁ P' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`.

Use `haveI : IsScalarTower B B' P' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Use `haveI : IsScalarTower B P P' := IsScalarTower.of_algebraMap_eq (fun b => (h b).symm)`. Set `t : P₁ ≃ₗ[P₁] P'` to `{ τ.toAddEquiv with map_smul' := fun a b => by show τ (a * b) = τ a * τ b`. Conclude with `map_mul τ a b }`. Set `e1 : P₁ ⊗[P] (P ⊗[B] M) ≃ₗ[P₁] P' ⊗[P] (P ⊗[B] M)` to `TensorProduct.AlgebraTensorModule.congr t (LinearEquiv.refl P _)`.

Set `e2 : P' ⊗[P] (P ⊗[B] M) ≃ₗ[P'] P' ⊗[B] M` to `TensorProduct.AlgebraTensorModule.cancelBaseChange B P P' P' M`. Set `e3 : P' ⊗[B'] (B' ⊗[B] M) ≃ₗ[P'] P' ⊗[B] M` to `TensorProduct.AlgebraTensorModule.cancelBaseChange B B' P' P' M`. Set `e4 : P' ⊗[B'] (B' ⊗[B] M) ≃ₗ[P'] P' ⊗[B'] M'` to `TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl P' P') μ`. Set `f` to `e2.trans (e3.symm.trans e4)`. Use `⟨e1.toAddEquiv.trans f.toAddEquiv, fun z w => ?_⟩` and prove the remaining obligations.

Use `show f (e1 (z • w)) = τ z • f (e1 w)`. Rewrite using `[map_smul, ← map_smul f]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Pa.BC.exists_semilinear_equiv_baseChange_tensor :
    ∀ (B P B' P₁ P' : Type) [CommRing B] [CommRing P] [CommRing B'] [CommRing P₁] [CommRing P'] [Algebra B P] [Algebra B B'] [Algebra P P₁] [Algebra B' P'] (τ : P₁ ≃+* P') (M M' : Type) [AddCommGroup M] [Module B M] [AddCommGroup M'] [Module B' M'] (_μ : B' ⊗[B] M ≃ₗ[B'] M'), (∀ b, τ (algebraMap P P₁ (algebraMap B P b)) = algebraMap B' P' (algebraMap B B' b)) → ∃ e : P₁ ⊗[P] (P ⊗[B] M) ≃+ P' ⊗[B'] M', ∀ z w, e (z • w) = τ z • e w := by
  intro B P B' P₁ P' _ _ _ _ _ _ _ _ _ τ M M' _ _ _ _ μ h
  letI : Algebra P₁ P' := τ.toRingHom.toAlgebra
  letI : Algebra P P' := (τ.toRingHom.comp (algebraMap P P₁)).toAlgebra
  letI : Algebra B P' := ((algebraMap B' P').comp (algebraMap B B')).toAlgebra
  haveI : IsScalarTower P P₁ P' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower B B' P' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower B P P' := IsScalarTower.of_algebraMap_eq (fun b => (h b).symm)
  let t : P₁ ≃ₗ[P₁] P' :=
    { τ.toAddEquiv with
      map_smul' := fun a b => by
        show τ (a * b) = τ a * τ b
        exact map_mul τ a b }
  let e1 : P₁ ⊗[P] (P ⊗[B] M) ≃ₗ[P₁] P' ⊗[P] (P ⊗[B] M) :=
    TensorProduct.AlgebraTensorModule.congr t (LinearEquiv.refl P _)
  let e2 : P' ⊗[P] (P ⊗[B] M) ≃ₗ[P'] P' ⊗[B] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange B P P' P' M
  let e3 : P' ⊗[B'] (B' ⊗[B] M) ≃ₗ[P'] P' ⊗[B] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange B B' P' P' M
  let e4 : P' ⊗[B'] (B' ⊗[B] M) ≃ₗ[P'] P' ⊗[B'] M' :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl P' P') μ
  let f := e2.trans (e3.symm.trans e4)
  refine ⟨e1.toAddEquiv.trans f.toAddEquiv, fun z w => ?_⟩
  show f (e1 (z • w)) = τ z • f (e1 w)
  rw [map_smul, ← map_smul f]
  rfl
