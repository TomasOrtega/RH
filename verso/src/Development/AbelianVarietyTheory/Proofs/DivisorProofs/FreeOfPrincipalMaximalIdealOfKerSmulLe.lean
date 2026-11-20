import Mathlib
open NumberField
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem free_of_principal_maximalIdeal_of_ker_smul_le :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : R),
      IsLocalRing.maximalIdeal R = Ideal.span {x} →
      ∀ (N : Type 1) [AddCommGroup N] [Module R N], Module.Finite R N →
        (∀ n : N, x • n = 0 → n ∈ Ideal.span {a : R | x * a = 0} • (⊤ : Submodule R N)) →
        Module.Free R N := by
  intro R _ _ _ x hx N _ _ hfin hann
  haveI : Module.FinitePresentation R N := Module.finitePresentation_of_finite R N
  apply Module.free_of_maximalIdeal_rTensor_injective
  have hxm : x ∈ IsLocalRing.maximalIdeal R := hx ▸ Ideal.subset_span rfl
  let X : IsLocalRing.maximalIdeal R := ⟨x, hxm⟩
  have hrep : ∀ t : (IsLocalRing.maximalIdeal R) ⊗[R] N, ∃ n : N, t = X ⊗ₜ n := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul m n =>
      obtain ⟨r, hr⟩ : ∃ r, r * x = (m : R) := by
        have hm : (m : R) ∈ Ideal.span {x} := hx ▸ m.2
        rwa [Ideal.mem_span_singleton'] at hm
      refine ⟨r • n, ?_⟩
      rw [← TensorProduct.smul_tmul]
      congr 1; ext; simp [X, hr]
    | add a b ha hb =>
      obtain ⟨n1, rfl⟩ := ha; obtain ⟨n2, rfl⟩ := hb
      exact ⟨n1 + n2, by rw [TensorProduct.tmul_add]⟩
  have hspan : ∀ a ∈ Ideal.span {a : R | x * a = 0}, x * a = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, hy, hz, add_zero]
    | smul c y _ hy => rw [smul_eq_mul, mul_left_comm, hy, mul_zero]
  have hzero : ∀ n ∈ Ideal.span {a : R | x * a = 0} • (⊤ : Submodule R N),
      (X ⊗ₜ[R] n : (IsLocalRing.maximalIdeal R) ⊗[R] N) = 0 := by
    intro n hn
    refine Submodule.smul_induction_on hn ?_ ?_
    · intro a ha m _
      rw [← TensorProduct.smul_tmul]
      have : a • X = 0 := by ext; simp [X, mul_comm a x, hspan a ha]
      rw [this, TensorProduct.zero_tmul]
    · intro m1 m2 h1 h2
      rw [TensorProduct.tmul_add, h1, h2, add_zero]
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨n, rfl⟩ := hrep t
  have hxn : x • n = 0 := by
    have h2 := congrArg (TensorProduct.lid R N) ht
    simpa [X] using h2
  exact hzero n (hann n hxn)

end GlobalTheory
