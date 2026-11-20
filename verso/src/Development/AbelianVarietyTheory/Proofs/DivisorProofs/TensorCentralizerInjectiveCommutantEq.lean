import Mathlib
open scoped TensorProduct Classical

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Normalize the expressions using the abelian group laws. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem tensor_centralizer_flat : ∀ (K : Type) [Field K] [Algebra ℚ K] (C : Type) [Ring C] [Algebra ℚ C] (y : C),
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.centralizer ℚ ({y} : Set C)).val) ∧
    ∀ w : K ⊗[ℚ] C, Commute w ((1 : K) ⊗ₜ[ℚ] y) → ∃ w' : K ⊗[ℚ] (Subalgebra.centralizer ℚ ({y} : Set C)),
      Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.centralizer ℚ ({y} : Set C)).val w' = w := by
  intro K _ _ C _ _ y
  set Z := Subalgebra.centralizer ℚ ({y} : Set C) with hZ
  have hmap : ∀ w', Algebra.TensorProduct.map (AlgHom.id K K) Z.val w'
      = LinearMap.lTensor K Z.val.toLinearMap w' := by
    intro w'
    induction w' using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  let ad : C →ₗ[ℚ] C := LinearMap.mulRight ℚ y - LinearMap.mulLeft ℚ y
  have hex : Function.Exact Z.val.toLinearMap ad := by
    intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have : x * g - g * x = 0 := by simpa [ad] using hx
      exact (sub_eq_zero.mp this).symm
    · rintro ⟨z, rfl⟩
      have hz := z.2
      rw [Subalgebra.mem_centralizer_iff] at hz
      have := hz y (Set.mem_singleton y)
      simp [ad, this]
  have hexK := Module.Flat.lTensor_exact K hex
  have hadK : ∀ w : K ⊗[ℚ] C, LinearMap.lTensor K ad w = w * ((1 : K) ⊗ₜ[ℚ] y) - ((1 : K) ⊗ₜ[ℚ] y) * w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [ad, TensorProduct.tmul_sub]
    | add a b ha hb => rw [map_add, ha, hb, add_mul, mul_add]; abel
  refine ⟨?_, ?_⟩
  · intro a b hab
    rw [hmap, hmap] at hab
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective hab
  · intro w hw
    have h0 : LinearMap.lTensor K ad w = 0 := by
      rw [hadK, hw.eq, sub_self]
    obtain ⟨w', hw'⟩ := (hexK w).mp h0
    exact ⟨w', by rw [hmap]; exact hw'⟩

end GlobalTheory
