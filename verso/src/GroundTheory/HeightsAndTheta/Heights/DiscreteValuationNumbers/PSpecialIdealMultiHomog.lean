import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

attribute [local instance] MvPolynomial.weightedGradedAlgebra

universe u

/- English proof (translation)
Introduce `d hd`. Rewrite `hd` using `[coeff_map]`. Apply `hp` to reduce the goal to its premises. Introduce `h0`. Conclude with `hd (by rw [h0, map_zero])`.
-/
theorem isWeightedHomogeneous_map_of {σ M R S : Type*} [AddCommMonoid M] [CommRing R]
    [CommRing S] (f : R →+* S) (w : σ → M) {p : MvPolynomial σ R} {b : M}
    (hp : IsWeightedHomogeneous w p b) : IsWeightedHomogeneous w (MvPolynomial.map f p) b := by
  intro d hd
  rw [coeff_map] at hd
  apply hp
  intro h0
  exact hd (by rw [h0, map_zero])

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.span_le]`. Conclude with `fun f hf => hf.1`. Introduce `p hp`. Rewrite using `[← sum_weightedHomogeneousComponent (w := blockWeight ι) p, finsum_eq_sum _ (weightedHomogeneousComponent_finsupp p)]`.

Use `Ideal.sum_mem _ fun m _ => Ideal.subset_span ⟨hP p hp m, m, ?_⟩` and prove the remaining obligations. Conclude with `weightedHomogeneousComponent_isWeightedHomogeneous m p`.
-/
theorem span_forms_of_isMultiHomogIdeal {K : Type} [DecidableEq K] {ι : K → Type}
    {R : Type*} [CommRing R] {P : Ideal (MRing ι R)} (hP : IsMultiHomogIdeal P) :
    Ideal.span {f | f ∈ P ∧ ∃ b, IsWeightedHomogeneous (blockWeight ι) f b} = P := by
  apply le_antisymm
  · rw [Ideal.span_le]
    exact fun f hf => hf.1
  · intro p hp
    rw [← sum_weightedHomogeneousComponent (w := blockWeight ι) p,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp p)]
    refine Ideal.sum_mem _ fun m _ => Ideal.subset_span ⟨hP p hp m, m, ?_⟩
    exact weightedHomogeneousComponent_isWeightedHomogeneous m p

/- English proof (translation)
Introduce `O _ _ _ K _ ι P hP`. Establish `hspan : specialIdeal P = Ideal.span (MvPolynomial.map (IsLocalRing.residue O) '' {f | f ∈ P ∧ ∃ b, IsWeightedHomogeneous (blockWeight ι) f b})`. Rewrite using `[specialIdeal, ← Ideal.map_span, span_forms_of_isMultiHomogIdeal hP]`. Establish `hhom : (specialIdeal P).IsHomogeneous (weightedHomogeneousSubmodule (IsLocalRing.ResidueField O) (blockWeight ι))`. Rewrite using `[hspan]`.

Apply `Ideal.homogeneous_span` to reduce the goal to its premises. Introduce and unpack `_ ⟨f, ⟨_, b, hb⟩, rfl⟩`. Conclude with `⟨b, (mem_weightedHomogeneousSubmodule _ _ _ _).2 (isWeightedHomogeneous_map_of _ _ hb)⟩`. Introduce `f hf b`. Conclude with `weightedHomogeneousComponent_mem_of_mem _ _ hhom hf b`.
-/
theorem SpecialIdealMultiHomog.proof : SpecialIdealMultiHomog.Statement := by
  classical
  intro O _ _ _ K _ ι P hP
  have hspan : specialIdeal P = Ideal.span
      (MvPolynomial.map (IsLocalRing.residue O) ''
        {f | f ∈ P ∧ ∃ b, IsWeightedHomogeneous (blockWeight ι) f b}) := by
    rw [specialIdeal, ← Ideal.map_span, span_forms_of_isMultiHomogIdeal hP]
  have hhom : (specialIdeal P).IsHomogeneous
      (weightedHomogeneousSubmodule (IsLocalRing.ResidueField O) (blockWeight ι)) := by
    rw [hspan]
    apply Ideal.homogeneous_span
    rintro _ ⟨f, ⟨_, b, hb⟩, rfl⟩
    exact ⟨b, (mem_weightedHomogeneousSubmodule _ _ _ _).2
      (isWeightedHomogeneous_map_of _ _ hb)⟩
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem _ _ hhom hf b

end GroundTheory.Heights₂.Heights.NumbersDVR
