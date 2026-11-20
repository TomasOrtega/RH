import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericPrimitive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

open MvPolynomial

def linearFormPoly {k : Type*} [Field k] {n : ℕ} (φ : (Fin n → k) →ₗ[k] k) : MvPolynomial (Fin n) k :=
  ∑ j, C (φ (Pi.single j 1)) * X j

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem eval_linearFormPoly {k : Type*} [Field k] {n : ℕ} (φ : (Fin n → k) →ₗ[k] k) (c : Fin n → k) :
    eval c (linearFormPoly φ) = φ c := by
  have hc : c = ∑ j, c j • (Pi.single j 1 : Fin n → k) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hc]
  simp [linearFormPoly, map_sum, mul_comm]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Supply the required witnesses or components.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem GenericPrimitive.proof : GenericPrimitive.Statement := by
  intro k K L _ _ _ _ _ _ _ _ _ n x hx
  have hfin : Finite (IntermediateField K L) :=
    Field.finite_intermediateField_of_exists_primitive_element K L (Field.exists_primitive_element K L)
  have := Fintype.ofFinite (IntermediateField K L)
  classical

  let f : (Fin n → k) →ₗ[k] L := Fintype.linearCombination k x
  have hf : ∀ c, f c = ∑ j, c j • x j := fun c => Fintype.linearCombination_apply k x c

  let W : IntermediateField K L → Submodule k (Fin n → k) := fun M =>
    (M.toSubalgebra.toSubmodule.restrictScalars k).comap f
  have hW : ∀ M : IntermediateField K L, M ≠ ⊤ → W M < ⊤ := by
    intro M hM
    refine lt_top_iff_ne_top.2 fun htop => hM ?_
    have hxM : Set.range x ⊆ M := by
      rintro _ ⟨j, rfl⟩
      have hj : (Pi.single j 1 : Fin n → k) ∈ W M := htop ▸ Submodule.mem_top
      have : f (Pi.single j 1) = x j := by
        rw [hf]; simp [Pi.single_apply]
      simpa [W, this] using hj
    exact eq_top_iff.2 (hx ▸ IntermediateField.adjoin_le_iff.2 hxM)
  have hφ : ∀ M : IntermediateField K L, ∃ φ : (Fin n → k) →ₗ[k] k,
      M ≠ ⊤ → φ ≠ 0 ∧ W M ≤ LinearMap.ker φ := by
    intro M
    by_cases hM : M = ⊤
    · exact ⟨0, fun h => (h hM).elim⟩
    · obtain ⟨φ, h0, hle⟩ := (W M).exists_le_ker_of_lt_top (hW M hM)
      exact ⟨φ, fun _ => ⟨h0, hle⟩⟩
  choose φ hφ using hφ
  let S : Finset (IntermediateField K L) := Finset.univ.filter (· ≠ ⊤)
  refine ⟨∏ M ∈ S, linearFormPoly (φ M), ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro M hM
    have hM' : M ≠ ⊤ := (Finset.mem_filter.1 hM).2
    obtain ⟨c, hc⟩ : ∃ c, φ M c ≠ 0 := by
      by_contra h
      exact (hφ M hM').1 (LinearMap.ext fun c => by simpa using not_not.1 (not_exists.1 h c))
    intro h0
    apply hc
    rw [← eval_linearFormPoly, h0, map_zero]
  · intro c hc
    by_contra hne
    rw [map_prod, Finset.prod_ne_zero_iff] at hc
    have hmem : IntermediateField.adjoin K {∑ j, c j • x j} ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩
    apply hc _ hmem
    rw [eval_linearFormPoly]
    apply (hφ _ hne).2
    show f c ∈ IntermediateField.adjoin K {∑ j, c j • x j}
    rw [hf]
    exact IntermediateField.mem_adjoin_simple_self K _

end

end GroundTheory.Heights₂.Heights.ComplexSets
