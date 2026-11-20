import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

/- English proof (translation)
Use `conv_rhs => rw [← sum_weightedHomogeneousComponent (coordDeg n) f]`. Use `(finsum_eq_sum_of_support_subset _ ?_).symm` and prove the remaining obligations. Introduce `m hm`. Rewrite `hm` using `[Function.mem_support]`. Rewrite using `[Finset.coe_image, Set.mem_image]`.

Assume the negation of the conclusion as `h`. Use `hm (weightedHomogeneousComponent_eq_zero' m f fun d hd hdm ↦ h ⟨d, hd, hdm⟩)` and prove the remaining obligations.
-/
theorem sum_weightedHomogeneousComponent_image (f : MvPolynomial (Coord n) ℤ) :
    ∑ m ∈ f.support.image (Finsupp.weight (coordDeg n)), weightedHomogeneousComponent (coordDeg n) m f = f := by
  conv_rhs => rw [← sum_weightedHomogeneousComponent (coordDeg n) f]
  refine (finsum_eq_sum_of_support_subset _ ?_).symm
  intro m hm
  rw [Function.mem_support] at hm
  rw [Finset.coe_image, Set.mem_image]
  by_contra h
  refine hm (weightedHomogeneousComponent_eq_zero' m f fun d hd hdm ↦ h ⟨d, hd, hdm⟩)

/- English proof (translation)
Introduce `ι _ _ n P`. Take `⟨s, hs⟩` from `(IsNoetherian.noetherian P.ideal : P.ideal.FG)`. Set `S : Finset (MvPolynomial (Coord n) ℤ)` to `s.biUnion fun f ↦ (f.support.image (Finsupp.weight (coordDeg n))).image fun m ↦ weightedHomogeneousComponent (coordDeg n) m f`. Establish `hShom : ∀ g ∈ S, ∃ m : ι → ℕ, IsWeightedHomogeneous (coordDeg n) g m`. Introduce `g hg`.

Simplify using `only [S, Finset.mem_biUnion, Finset.mem_image] at hg`. Take `⟨f, -, m, -, rfl⟩` from `hg`. Conclude with `⟨m, weightedHomogeneousComponent_isWeightedHomogeneous m f⟩`. Establish `hSP : ∀ g ∈ S, g ∈ P.ideal`. Introduce `g hg`.

Simplify using `only [S, Finset.mem_biUnion, Finset.mem_image] at hg`. Take `⟨f, hf, m, -, rfl⟩` from `hg`. Conclude with `P.homogeneous f (hs ▸ Ideal.subset_span hf) m`. Set `e` to `S.equivFin`. Use `⟨S.card, fun i ↦ (e.symm i : MvPolynomial (Coord n) ℤ), fun i ↦ Classical.choose (hShom _ (e.symm i).2), ⟨fun i ↦ Classical.choose_spec (hShom _ (e.symm i).2), ?_⟩⟩` and prove the remaining obligations.

Establish `hrange : Set.range (fun i ↦ (e.symm i : MvPolynomial (Coord n) ℤ)) = (S : Set _)`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Conclude with `(e.symm i).2`.

Introduce `hg`. Conclude with `⟨e ⟨g, hg⟩, by simp⟩`. Rewrite using `[hrange]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.span_le]`.

Introduce `g hg`. Conclude with `hSP g hg`. Rewrite using `[← hs, Ideal.span_le]`. Introduce `f hf`. Rewrite using `[← sum_weightedHomogeneousComponent_image f]`.

Use `Ideal.sum_mem _ fun m hm ↦ Ideal.subset_span ?_` and prove the remaining obligations. Simplify using `only [S, Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image]`. Conclude with `⟨f, hf, m, by simpa using hm, rfl⟩`.
-/
theorem HomogGeneratorsExist.proof : HomogGeneratorsExist.Statement := by
  classical
  intro ι _ _ n P
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian P.ideal : P.ideal.FG)

  let S : Finset (MvPolynomial (Coord n) ℤ) := s.biUnion fun f ↦
    (f.support.image (Finsupp.weight (coordDeg n))).image fun m ↦ weightedHomogeneousComponent (coordDeg n) m f
  have hShom : ∀ g ∈ S, ∃ m : ι → ℕ, IsWeightedHomogeneous (coordDeg n) g m := by
    intro g hg
    simp only [S, Finset.mem_biUnion, Finset.mem_image] at hg
    obtain ⟨f, -, m, -, rfl⟩ := hg
    exact ⟨m, weightedHomogeneousComponent_isWeightedHomogeneous m f⟩
  have hSP : ∀ g ∈ S, g ∈ P.ideal := by
    intro g hg
    simp only [S, Finset.mem_biUnion, Finset.mem_image] at hg
    obtain ⟨f, hf, m, -, rfl⟩ := hg
    exact P.homogeneous f (hs ▸ Ideal.subset_span hf) m
  let e := S.equivFin
  refine ⟨S.card, fun i ↦ (e.symm i : MvPolynomial (Coord n) ℤ),
    fun i ↦ Classical.choose (hShom _ (e.symm i).2), ⟨fun i ↦ Classical.choose_spec (hShom _ (e.symm i).2), ?_⟩⟩
  have hrange : Set.range (fun i ↦ (e.symm i : MvPolynomial (Coord n) ℤ)) = (S : Set _) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp⟩
  rw [hrange]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro g hg
    exact hSP g hg
  · rw [← hs, Ideal.span_le]
    intro f hf
    rw [← sum_weightedHomogeneousComponent_image f]
    refine Ideal.sum_mem _ fun m hm ↦ Ideal.subset_span ?_
    simp only [S, Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image]
    exact ⟨f, hf, m, by simpa using hm, rfl⟩

end

end GroundTheory.Heights₂.Heights
