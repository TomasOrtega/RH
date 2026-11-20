import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open scoped Classical in

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem isHomogeneous_of_isMultiHomogIdeal' {K : Type*} [DecidableEq K] {ι : K → Type*}
    {R : Type*} [CommRing R] {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) :
    I.IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) := by
  classical
  have e : I = Ideal.span
      {g | ∃ f ∈ I, ∃ b, g = weightedHomogeneousComponent (blockWeight ι) b f} := by
    apply le_antisymm
    · intro f hf
      rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      exact Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨f, hf, b, rfl⟩
    · rw [Ideal.span_le]
      rintro g ⟨f, hf, b, rfl⟩
      exact hI f hf b
  rw [e]
  refine Ideal.homogeneous_span _ _ fun x hx => ?_
  obtain ⟨f, -, b, rfl⟩ := hx
  exact ⟨b, weightedHomogeneousComponent_isWeightedHomogeneous b f⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem SupSpanMultiHomog.proof : SupSpanMultiHomog.Statement := by
  classical
  intro R _ K _ ι I x e hI hx
  have h1 := isHomogeneous_of_isMultiHomogIdeal' hI
  have h2 : (Ideal.span {x}).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) :=
    Ideal.homogeneous_span _ _ (by
      rintro y rfl
      exact ⟨e, hx⟩)
  have h := h1.sup h2
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) h hf b

end GroundTheory.Heights₂.Heights.NumbersDVR
