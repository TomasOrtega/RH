import Mathlib

open TensorProduct in
/- English proof (translation)
Use `haveI : Nontrivial (κ₁ ⊗[K] κ₂) := inferInstance`. Take `⟨m, hm⟩` from `Ideal.exists_maximal (κ₁ ⊗[K] κ₂)`. Use `⟨(κ₁ ⊗[K] κ₂) ⧸ m, Ideal.Quotient.field m, (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeLeft : κ₁ →ₐ[K] κ₁ ⊗[K] κ₂).toRingHom, (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight : κ₂ →ₐ[K] κ₁ ⊗[K] κ₂).toRingHom, fun x => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk m ((Algebra.TensorProduct.includeLeft : κ₁ →ₐ[K] κ₁ ⊗[K] κ₂) (algebraMap K κ₁ x)) = Ideal.Quotient.mk m ((Algebra.TensorProduct.includeRight : κ₂ →ₐ[K] κ₁ ⊗[K] κ₂) (algebraMap K κ₂ x))`. Rewrite using `[AlgHom.commutes, AlgHom.commutes]`.
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
Introduce `B κ₁ κ₂ _ _ _ f₁ f₂ h`. Set `D` to `B ⧸ RingHom.ker f₁`. Use `haveI : (RingHom.ker f₁).IsPrime := RingHom.ker_isPrime f₁`. Use `haveI : IsDomain D := Ideal.Quotient.isDomain _`. Set `g₁ : D →+* κ₁` to `RingHom.kerLift f₁`.

Establish `hg₁ : Function.Injective g₁` using `RingHom.kerLift_injective f₁`. Set `g₂ : D →+* κ₂` to `(RingHom.kerLift f₂).comp (Ideal.quotEquivOfEq h).toRingHom`. Establish `hg₂ : Function.Injective g₂` using `(RingHom.kerLift_injective f₂).comp (Ideal.quotEquivOfEq h).injective`. Set `K` to `FractionRing D`. Use `letI : Algebra K κ₁ := (IsFractionRing.lift (K := K) hg₁).toAlgebra`.

Use `letI : Algebra K κ₂ := (IsFractionRing.lift (K := K) hg₂).toAlgebra`. Establish `e₁ : ∀ b : B, algebraMap K κ₁ (algebraMap D K (Ideal.Quotient.mk _ b)) = f₁ b` using `fun b => (IsFractionRing.lift_algebraMap hg₁ _).trans (RingHom.kerLift_mk f₁ b)`. Establish `e₂ : ∀ b : B, algebraMap K κ₂ (algebraMap D K (Ideal.Quotient.mk _ b)) = f₂ b` using `fun b => (IsFractionRing.lift_algebraMap hg₂ _).trans (RingHom.kerLift_mk f₂ b)`. Take `⟨κ, _, j₁, j₂, hj⟩` from `UpperTheory.Reformulated.B.Qe15.compositum K κ₁ κ₂`. Use `⟨κ, inferInstance, j₁, j₂, RingHom.ext fun b => ?_⟩` and prove the remaining obligations.

Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, ← e₁, ← e₂]`. Conclude with `hj _`.
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
