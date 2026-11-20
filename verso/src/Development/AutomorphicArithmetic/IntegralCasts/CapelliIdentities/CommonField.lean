import Mathlib

open TensorProduct in
/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem UpperTheory.Reformulated.B.Qe15.compositum (K κ₁ κ₂ : Type) [Field K] [Field κ₁] [Field κ₂]
    [Algebra K κ₁] [Algebra K κ₂] :
    ∃ (κ : Type) (_ : Field κ) (j₁ : κ₁ →+* κ) (j₂ : κ₂ →+* κ),
      ∀ x : K, j₁ (algebraMap K κ₁ x) = j₂ (algebraMap K κ₂ x) := by
  haveI : Nontrivial (κ₁ ⊗[K] κ₂) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (κ₁ ⊗[K] κ₂)
  refine ⟨(κ₁ ⊗[K] κ₂) ⧸ m, Ideal.Quotient.field m,
    (Ideal.Quotient.mk m).comp
      (Algebra.TensorProduct.includeLeft : κ₁ →ₐ[K] κ₁ ⊗[K] κ₂).toRingHom,
    (Ideal.Quotient.mk m).comp
      (Algebra.TensorProduct.includeRight : κ₂ →ₐ[K] κ₁ ⊗[K] κ₂).toRingHom, fun x => ?_⟩
  change Ideal.Quotient.mk m
      ((Algebra.TensorProduct.includeLeft : κ₁ →ₐ[K] κ₁ ⊗[K] κ₂) (algebraMap K κ₁ x)) =
    Ideal.Quotient.mk m
      ((Algebra.TensorProduct.includeRight : κ₂ →ₐ[K] κ₁ ⊗[K] κ₂) (algebraMap K κ₂ x))
  rw [AlgHom.commutes, AlgHom.commutes]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Introduce a local definition for the expression. Equip the data with the indicated structure. Equip the data with the indicated structure. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.Qe15.common_field :
    ∀ (B κ₁ κ₂ : Type) [inst : CommRing B] [inst_1 : Field κ₁] [inst_2 : Field κ₂]
    (f₁ : B →+* κ₁) (f₂ : B →+* κ₂),
    RingHom.ker f₁ = RingHom.ker f₂ →
      ∃ (κ : Type) (x : Field κ) (j₁ : κ₁ →+* κ) (j₂ : κ₂ →+* κ), j₁.comp f₁ = j₂.comp f₂ := by
  intro B κ₁ κ₂ _ _ _ f₁ f₂ h
  let D := B ⧸ RingHom.ker f₁
  haveI : (RingHom.ker f₁).IsPrime := RingHom.ker_isPrime f₁
  haveI : IsDomain D := Ideal.Quotient.isDomain _
  let g₁ : D →+* κ₁ := RingHom.kerLift f₁
  have hg₁ : Function.Injective g₁ := RingHom.kerLift_injective f₁
  let g₂ : D →+* κ₂ := (RingHom.kerLift f₂).comp (Ideal.quotEquivOfEq h).toRingHom
  have hg₂ : Function.Injective g₂ :=
    (RingHom.kerLift_injective f₂).comp (Ideal.quotEquivOfEq h).injective
  let K := FractionRing D
  letI : Algebra K κ₁ := (IsFractionRing.lift (K := K) hg₁).toAlgebra
  letI : Algebra K κ₂ := (IsFractionRing.lift (K := K) hg₂).toAlgebra
  have e₁ : ∀ b : B, algebraMap K κ₁ (algebraMap D K (Ideal.Quotient.mk _ b)) = f₁ b := fun b =>
    (IsFractionRing.lift_algebraMap hg₁ _).trans (RingHom.kerLift_mk f₁ b)
  have e₂ : ∀ b : B, algebraMap K κ₂ (algebraMap D K (Ideal.Quotient.mk _ b)) = f₂ b := fun b =>
    (IsFractionRing.lift_algebraMap hg₂ _).trans (RingHom.kerLift_mk f₂ b)
  obtain ⟨κ, _, j₁, j₂, hj⟩ := UpperTheory.Reformulated.B.Qe15.compositum K κ₁ κ₂
  refine ⟨κ, inferInstance, j₁, j₂, RingHom.ext fun b => ?_⟩
  rw [RingHom.comp_apply, RingHom.comp_apply, ← e₁, ← e₂]
  exact hj _
