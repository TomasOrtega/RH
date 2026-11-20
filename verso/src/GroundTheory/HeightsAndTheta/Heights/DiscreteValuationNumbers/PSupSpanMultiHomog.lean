import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open scoped Classical in

/- English proof (translation)
Establish `e : I = Ideal.span {g | ∃ f ∈ I, ∃ b, g = weightedHomogeneousComponent (blockWeight ι) b f}`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `f hf`. Rewrite using `[← sum_weightedHomogeneousComponent (blockWeight ι) f, finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]`. Conclude with `Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨f, hf, b, rfl⟩`.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `g ⟨f, hf, b, rfl⟩`. Conclude with `hI f hf b`. Rewrite using `[e]`. Use `Ideal.homogeneous_span _ _ fun x hx => ?_` and prove the remaining obligations.

Take `⟨f, -, b, rfl⟩` from `hx`. Conclude with `⟨b, weightedHomogeneousComponent_isWeightedHomogeneous b f⟩`.
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
Introduce `R _ K _ ι I x e hI hx`. Establish `h1` using `isHomogeneous_of_isMultiHomogIdeal' hI`. Establish `h2 : (Ideal.span {x}).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι))` using `Ideal.homogeneous_span _ _ (by`. Introduce and unpack `y rfl`. Conclude with `⟨e, hx⟩)`.

Establish `h` using `h1.sup h2`. Introduce `f hf b`. Conclude with `weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) h hf b`.
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
