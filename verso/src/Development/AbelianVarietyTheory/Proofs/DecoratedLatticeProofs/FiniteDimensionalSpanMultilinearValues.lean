import Mathlib

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem finiteDimensional_span_multilinear_values :
    ∀ {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
      (F : Type) [AddCommGroup F] [Module ℂ F] (T : MultilinearMap ℂ E F)
      (W : ∀ i, Submodule ℂ (E i)), (∀ i, FiniteDimensional ℂ (W i)) →
      FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ v : ∀ i, E i, (∀ i, v i ∈ W i) ∧ f = T v}) := by
  intro ι _ E _ _ F _ _ T W hW
  have := hW
  let T' : MultilinearMap ℂ (fun i => W i) F := T.compLinearMap (fun i => (W i).subtype)
  have hset : {f | ∃ v : ∀ i, E i, (∀ i, v i ∈ W i) ∧ f = T v} = Set.range T' := by
    ext f
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨fun i => ⟨v i, hv i⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨fun i => (w i : E i), fun i => (w i).2, rfl⟩
  have hle : Submodule.span ℂ (Set.range T') ≤ LinearMap.range (PiTensorProduct.lift T') := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact ⟨PiTensorProduct.tprod ℂ w, by simp⟩
  rw [hset]
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory
