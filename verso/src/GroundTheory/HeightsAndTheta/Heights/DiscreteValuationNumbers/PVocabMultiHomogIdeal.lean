import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBridge
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem VocabMultiHomogIdeal.proof (h1 : VocabMultiHomog.Statement.{u}) :
    VocabMultiHomogIdeal.Statement.{u} := by
  intro R _ K _ _ ι _ P
  let := weightedGradedAlgebra R (blockWeight ι)
  constructor
  · rintro ⟨S, hS, rfl⟩
    have hhom : (Ideal.span S).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) := by
      refine Ideal.homogeneous_span (weightedHomogeneousSubmodule R (blockWeight ι)) S
        fun x hx => ?_
      obtain ⟨a, ha⟩ := hS x hx
      exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).2 ((h1 R K ι x a).1 ha)⟩
    intro f hf b
    exact weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) hhom hf b
  · intro hP
    refine ⟨{c | ∃ f ∈ P, ∃ b, c = weightedHomogeneousComponent (blockWeight ι) b f}, ?_, ?_⟩
    · rintro c ⟨f, -, b, rfl⟩
      exact ⟨b, (h1 R K ι _ b).2 (weightedHomogeneousComponent_isWeightedHomogeneous b f)⟩
    · apply le_antisymm
      · intro f hf
        rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
          finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
        exact Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨f, hf, b, rfl⟩
      · rw [Ideal.span_le]
        rintro c ⟨f, hf, b, rfl⟩
        exact hP f hf b

end GroundTheory.Heights₂.Heights.NumbersDVR
