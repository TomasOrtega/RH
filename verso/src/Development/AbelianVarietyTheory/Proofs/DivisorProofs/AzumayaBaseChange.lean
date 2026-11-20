import Mathlib
open scoped TensorProduct
open Function

namespace GlobalTheory
open TensorProduct MulOpposite

variable (A S Λ : Type) [CommRing A] [CommRing S] [Algebra A S] [Ring Λ] [Algebra A Λ]

noncomputable def endBaseChangeMap :
    S ⊗[A] Module.End A Λ →ₗ[S] Module.End S (S ⊗[A] Λ) :=
  (LinearMap.baseChangeHom A S Λ Λ).liftBaseChange S

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma endBaseChangeMap_tmul (s : S) (f : Module.End A Λ) :
    endBaseChangeMap A S Λ (s ⊗ₜ f) = s • f.baseChange S := by
  simp [endBaseChangeMap]

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma endBaseChangeMap_bijective [Module.Free A Λ] [Module.Finite A Λ] :
    Bijective (endBaseChangeMap A S Λ) := by
  classical
  let ι := Module.Free.ChooseBasisIndex A Λ
  let b := Module.Free.chooseBasis A Λ
  let bS := Algebra.TensorProduct.basis S b
  let e₁ : S ⊗[A] Module.End A Λ ≃ₗ[S] S ⊗[A] Matrix ι ι A :=
    (LinearMap.toMatrix b b).baseChange A S _ _
  let e₂ := (matrixEquivTensor ι A S).symm
  let e₃ := LinearMap.toMatrix bS bS
  have h : ∀ x, e₃ (endBaseChangeMap A S Λ x) = e₂ (e₁ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s f =>
      simp [e₁, e₂, e₃, bS, endBaseChangeMap_tmul, matrixEquivTensor_apply_symm]
    | add x y hx hy => simp only [map_add, hx, hy]
  have : (endBaseChangeMap A S Λ : _ → _) = e₃.symm ∘ e₂ ∘ e₁ := by
    funext x; simp [← h x]
  rw [this]
  exact e₃.symm.bijective.comp (e₂.bijective.comp e₁.bijective)

noncomputable def opBaseChange : S ⊗[A] Λᵐᵒᵖ ≃ₗ[S] (S ⊗[A] Λ)ᵐᵒᵖ :=
  ((opLinearEquiv A (M := Λ)).symm.baseChange A S _ _).trans (opLinearEquiv S)

noncomputable def envBaseChange :
    S ⊗[A] (Λ ⊗[A] Λᵐᵒᵖ) ≃ₗ[S] (S ⊗[A] Λ) ⊗[S] (S ⊗[A] Λ)ᵐᵒᵖ :=
  (AlgebraTensorModule.distribBaseChange A S Λ Λᵐᵒᵖ).trans
    (TensorProduct.congr (LinearEquiv.refl S _) (opBaseChange A S Λ))

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Proceed by induction.

Treat this case separately. Treat this case separately. Treat this case separately. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.
-/
lemma mulLeftRight_envBaseChange (x : S ⊗[A] (Λ ⊗[A] Λᵐᵒᵖ)) :
    AlgHom.mulLeftRight S (S ⊗[A] Λ) (envBaseChange A S Λ x) =
      endBaseChangeMap A S Λ ((AlgHom.mulLeftRight A Λ).toLinearMap.lTensor S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
    | tmul a b =>
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [map_add, hz, hw]
      | tmul t y =>
        simp [envBaseChange, opBaseChange, endBaseChangeMap_tmul,
          AlgebraTensorModule.distribBaseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          smul_tmul', mul_comm, mul_left_comm]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isAzumaya_baseChange [IsAzumaya A Λ] [Module.Free A Λ] :
    IsAzumaya S (S ⊗[A] Λ) := by
  classical
  haveI : Module.Finite A Λ := inferInstance
  refine { toProjective := inferInstance, toFinite := inferInstance,
           toFaithfulSMul := ?_, bij := ?_ }
  · rcases subsingleton_or_nontrivial S with hS | hS
    · exact ⟨fun _ => Subsingleton.elim _ _⟩
    · haveI : Nontrivial A := (algebraMap A S).domain_nontrivial
      haveI : Nontrivial Λ := by
        by_contra hΛ
        rw [not_nontrivial_iff_subsingleton] at hΛ
        have : (0 : A) = 1 :=
          FaithfulSMul.eq_of_smul_eq_smul (α := Λ) fun _ => Subsingleton.elim _ _
        exact zero_ne_one this
      let b := Module.Free.chooseBasis A Λ
      let bS := Algebra.TensorProduct.basis S b
      obtain ⟨i⟩ := b.index_nonempty
      refine ⟨fun {s₁ s₂} h => ?_⟩
      have := congrArg (fun x => bS.repr x i) (h (bS i))
      simpa using this
  · have hφ : Bijective ((AlgHom.mulLeftRight A Λ).toLinearMap.lTensor S) := by
      let e := LinearEquiv.ofBijective (AlgHom.mulLeftRight A Λ).toLinearMap IsAzumaya.bij
      have : (AlgHom.mulLeftRight A Λ).toLinearMap.lTensor S = (e.lTensor S : _ →ₗ[A] _) := rfl
      rw [this]; exact (e.lTensor S).bijective
    have hc : (AlgHom.mulLeftRight S (S ⊗[A] Λ) : _ → _) =
        (endBaseChangeMap A S Λ ∘ (AlgHom.mulLeftRight A Λ).toLinearMap.lTensor S) ∘
          (envBaseChange A S Λ).symm := by
      funext y
      simp [← mulLeftRight_envBaseChange]
    rw [hc]
    exact ((endBaseChangeMap_bijective A S Λ).comp hφ).comp (envBaseChange A S Λ).symm.bijective

end GlobalTheory
