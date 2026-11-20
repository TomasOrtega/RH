import Mathlib

open CategoryTheory TensorProduct ChangeOfRings

namespace GlobalTheory.CompanionTheory.ModuleReduction

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Treat this case separately. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem mem_smul_of_tmul_eq_zero {A Q N : Type} [CommRing A] [AddCommGroup Q] [Module A Q]
    [AddCommGroup N] [Module A N] (g : A →ₗ[A] Q) (hg : Function.Surjective g) (ξ : A)
    (hk : ∀ a, g a = 0 ↔ ∃ b, a = ξ * b) (m : N) (h : g 1 ⊗ₜ[A] m = 0) :
    ∃ n : N, m = ξ • n := by
  have hex : Function.Exact (LinearMap.mulLeft A ξ) g := by
    intro a
    rw [hk a]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b, rfl⟩
  have hex' := rTensor_exact N hex hg
  have h1 : (LinearMap.rTensor N g) ((1 : A) ⊗ₜ[A] m) = 0 := by
    simpa using h
  obtain ⟨t, ht⟩ := (hex' _).1 h1
  have key : ∀ t : A ⊗[A] N, TensorProduct.lid A N (LinearMap.rTensor N (LinearMap.mulLeft A ξ) t)
      = ξ • TensorProduct.lid A N t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a n => simp [mul_smul]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  refine ⟨TensorProduct.lid A N t, ?_⟩
  rw [← key, ht]
  simp

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Express the relevant assertion in an equivalent form by its definition. Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem exists_reduction (A O : Type) [CommRing A] [CommRing O] (θ : A →+* O)
    (hθ : Function.Surjective θ) (ξ : A) (hker : RingHom.ker θ = Ideal.span {ξ})
    (𝒞 : Type 1) [CategoryTheory.Category.{0} 𝒞] (M : CategoryTheory.Functor 𝒞 (ModuleCat.{0} A)) :
    ∃ (D : CategoryTheory.Functor 𝒞 (ModuleCat.{0} O)) (r : ∀ X : 𝒞, M.obj X →ₛₗ[θ] D.obj X),
      (∀ X, Function.Surjective (r X) ∧ ∀ m, r X m = 0 ↔ ∃ n, m = ξ • n) ∧
      ∀ (X Y : 𝒞) (f : X ⟶ Y) (m : M.obj X), D.map f (r X m) = r Y (M.map f m) := by
  let Q := (ModuleCat.restrictScalars θ).obj (ModuleCat.of O O)
  let one : Q := (1 : O)
  let g : A →ₗ[A] Q := LinearMap.toSpanSingleton A Q one
  have hgθ : ∀ a, (g a : O) = θ a := fun a => mul_one (θ a)
  have hsm : ∀ (X : 𝒞) (a : A) (m : M.obj X),
      (1 : O) ⊗ₜ[A,θ] (a • m) = (θ a) ⊗ₜ[A,θ] m := by
    intro X a m
    have h := TensorProduct.smul_tmul (R := A) (R' := A) a one m
    have e : a • one = (θ a : O) := hgθ a
    rw [e] at h
    exact h.symm
  let r : ∀ X : 𝒞, M.obj X →ₛₗ[θ] (M ⋙ ModuleCat.extendScalars θ).obj X := fun X =>
    { toFun := fun m => (1 : O) ⊗ₜ[A,θ] m
      map_add' := fun a b => TensorProduct.tmul_add _ _ _
      map_smul' := fun a m => by
        refine (hsm X a m).trans ?_
        have := ModuleCat.ExtendScalars.smul_tmul θ (M := M.obj X) (θ a) (1 : O) m
        rw [mul_one] at this
        exact this.symm }
  refine ⟨M ⋙ ModuleCat.extendScalars θ, r, fun X => ⟨?_, fun m => ⟨?_, ?_⟩⟩, ?_⟩
  · intro y
    change Q ⊗[A] (M.obj X) at y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul o n =>
      obtain ⟨a, ha⟩ := hθ o
      refine ⟨a • n, ?_⟩
      refine (hsm X a n).trans ?_
      rw [ha]
      rfl
    | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      refine ⟨u + v, ?_⟩
      rw [map_add, hu, hv]
      rfl
  · intro h
    refine mem_smul_of_tmul_eq_zero g ?_ ξ ?_ m ?_
    · intro q
      obtain ⟨a, ha⟩ := hθ q
      exact ⟨a, (hgθ a).trans ha⟩
    · intro a
      have : g a = 0 ↔ θ a = 0 := by
        rw [← hgθ a]
        rfl
      rw [this, ← RingHom.mem_ker, hker, Ideal.mem_span_singleton']
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨b, mul_comm _ _⟩
      · rintro ⟨b, rfl⟩
        exact ⟨b, mul_comm _ _⟩
    · have e : g 1 = one := one_smul A one
      rw [e]
      exact h
  · rintro ⟨n, rfl⟩
    have : θ ξ = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact Ideal.mem_span_singleton_self ξ
    change (1 : O) ⊗ₜ[A,θ] (ξ • n) = 0
    rw [hsm X ξ n, this]
    exact TensorProduct.zero_tmul (R := A) Q n
  · intro X Y f m
    rfl

end GlobalTheory.CompanionTheory.ModuleReduction
