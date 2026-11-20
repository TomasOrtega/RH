import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBridge
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Introduce `R _ K _ _ ι _ P`. Set `` to `weightedGradedAlgebra R (blockWeight ι)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨S, hS, rfl⟩`. Establish `hhom : (Ideal.span S).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι))`.

Use `Ideal.homogeneous_span (weightedHomogeneousSubmodule R (blockWeight ι)) S fun x hx => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `hS x hx`. Conclude with `⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).2 ((h1 R K ι x a).1 ha)⟩`. Introduce `f hf b`. Conclude with `weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) hhom hf b`.

Introduce `hP`. Use `⟨{c | ∃ f ∈ P, ∃ b, c = weightedHomogeneousComponent (blockWeight ι) b f}, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `c ⟨f, -, b, rfl⟩`. Conclude with `⟨b, (h1 R K ι _ b).2 (weightedHomogeneousComponent_isWeightedHomogeneous b f)⟩`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `f hf`. Rewrite using `[← sum_weightedHomogeneousComponent (blockWeight ι) f, finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]`. Conclude with `Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨f, hf, b, rfl⟩`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `c ⟨f, hf, b, rfl⟩`.

Conclude with `hP f hf b`.
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
