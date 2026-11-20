import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LocCycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Unfold `divCycle at h`. Use `split_ifs at h with hW`. Take `⟨hmin, hrel⟩` from `hW`. Use `⟨hmin.1.1, hrel, le_trans le_sup_left hmin.1.2, ?_⟩` and prove the remaining obligations. Conclude with `MinimalPrimeMultiHomog.proof O K ι _ W (SupSpanMultiHomog.proof O K ι P f e hP hf) hmin`.

Conclude with `absurd rfl h`.
-/
theorem divCycle_ne_zero_facts {O : Type u} [CommRing O] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} {P : Ideal (MRing ι O)} (hP : IsMultiHomogIdeal P) {f : MRing ι O} {e : K → ℕ}
    (hf : IsMultiHomog f e) {W : Ideal (MRing ι O)} (h : divCycle P f W ≠ 0) :
    W.IsPrime ∧ IsRelevant W ∧ P ≤ W ∧ IsMultiHomogIdeal W := by
  unfold divCycle at h
  split_ifs at h with hW
  · obtain ⟨hmin, hrel⟩ := hW
    refine ⟨hmin.1.1, hrel, le_trans le_sup_left hmin.1.2, ?_⟩
    exact MinimalPrimeMultiHomog.proof O K ι _ W (SupSpanMultiHomog.proof O K ι P f e hP hf) hmin
  · exact absurd rfl h

/- English proof (translation)
Introduce `O _ _ _ ϖ K _ _ ι _ P hP b f g hD c s hs G U hU`. Assume the negation of the conclusion as `hne`. Apply `hU` to reduce the goal to its premises. Establish `hG : ratDiv P f g G ≠ 0` using `left_ne_zero_of_mul hne`. Establish `hU' : divCycle G s U ≠ 0` using `right_ne_zero_of_mul hne`.

Establish `hϖG : (C ϖ : MRing ι O) ∈ G` using `hD.vertical G hG`. Take `⟨bf, bg, hf, hg, -⟩` from `hD.degrees`. Establish `hGfacts : P ≤ G ∧ IsMultiHomogIdeal G`. Establish `: divCycle P f G ≠ 0 ∨ divCycle P g G ≠ 0`. Assume the negation of the conclusion as `h`.

Rewrite `h` using `[not_or, not_not, not_not]`. Conclude with `hG (by unfold ratDiv; rw [h.1, h.2, sub_zero])`. Break down `this with h | h` into its components or cases. Conclude with `(divCycle_ne_zero_facts hP hf h).2.2`. Conclude with `(divCycle_ne_zero_facts hP hg h).2.2`.

Take `⟨hUp, hUr, hGU, hUm⟩` from `divCycle_ne_zero_facts hGfacts.2 hs hU'`. Conclude with `⟨hUp, hUm, hUr, hGU hϖG, le_trans hGfacts.1 hGU⟩`.
-/
theorem LeftTermSupport.proof : LeftTermSupport.Statement.{u} := by
  intro O _ _ _ ϖ K _ _ ι _ P hP b f g hD c s hs G U hU
  by_contra hne
  apply hU
  have hG : ratDiv P f g G ≠ 0 := left_ne_zero_of_mul hne
  have hU' : divCycle G s U ≠ 0 := right_ne_zero_of_mul hne
  have hϖG : (C ϖ : MRing ι O) ∈ G := hD.vertical G hG
  obtain ⟨bf, bg, hf, hg, -⟩ := hD.degrees
  have hGfacts : P ≤ G ∧ IsMultiHomogIdeal G := by
    have : divCycle P f G ≠ 0 ∨ divCycle P g G ≠ 0 := by
      by_contra h
      rw [not_or, not_not, not_not] at h
      exact hG (by unfold ratDiv; rw [h.1, h.2, sub_zero])
    rcases this with h | h
    · exact (divCycle_ne_zero_facts hP hf h).2.2
    · exact (divCycle_ne_zero_facts hP hg h).2.2
  obtain ⟨hUp, hUr, hGU, hUm⟩ := divCycle_ne_zero_facts hGfacts.2 hs hU'
  exact ⟨hUp, hUm, hUr, hGU hϖG, le_trans hGfacts.1 hGU⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
