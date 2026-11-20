import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreCriterion
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalLocalDepthTwo
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Imports
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

/- English proof (translation)
Distinguish the cases in `hf : IsField B`. Set `` to `hf.toField infer_instance`. Establish `: Ring.KrullDimLE 1 B` using `Ring.krullDimLE_iff.mpr (by exact_mod_cast h)`. Establish `hm : maximalIdeal B ≠ ⊥` using `fun hm => hf (isField_iff_maximalIdeal_eq.mpr hm)`. Establish `h3 : IsIntegrallyClosed B ∧ ∃! P : Ideal B, P ≠ ⊥ ∧ P.IsPrime` using `⟨inferInstance, maximalIdeal B, ⟨hm, inferInstance⟩, fun P ⟨hP, hPp⟩ => IsLocalRing.eq_maximalIdeal (hPp.isMaximal_of_ne_bot hP)⟩`.

Establish `hdvr : IsDiscreteValuationRing B` using `((IsDiscreteValuationRing.TFAE B hf).out 0 3).mpr h3`. Use `infer_instance`.
-/
theorem isRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_le_one (B : Type*) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B] (h : ringKrullDim B ≤ 1) : IsRegularLocalRing B := by
  by_cases hf : IsField B
  · let := hf.toField
    infer_instance
  · have : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.mpr (by exact_mod_cast h)
    have hm : maximalIdeal B ≠ ⊥ := fun hm => hf (isField_iff_maximalIdeal_eq.mpr hm)
    have h3 : IsIntegrallyClosed B ∧ ∃! P : Ideal B, P ≠ ⊥ ∧ P.IsPrime :=
      ⟨inferInstance, maximalIdeal B, ⟨hm, inferInstance⟩, fun P ⟨hP, hPp⟩ =>
        IsLocalRing.eq_maximalIdeal (hPp.isMaximal_of_ne_bot hP)⟩
    have hdvr : IsDiscreteValuationRing B := ((IsDiscreteValuationRing.TFAE B hf).out 0 3).mpr h3
    infer_instance

/- English proof (translation)
Introduce `A _ hA`. Use `⟨fun h => ⟨fun P _ hdim => ?_, fun P _ => ?_⟩, fun h => hN A hA h.1 h.2⟩` and prove the remaining obligations. Take `⟨hd, hi⟩` from `h P`. Conclude with `isRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_le_one _ (by exact_mod_cast hdim)`. Take `⟨hd, hi⟩` from `h P`.

Conclude with `hS _`.
-/
theorem SerreCriterion.proof (hS : NormalLocalDepthTwo.Statement) (hN : SerreNormalOfRegularDepth.Statement) :
    SerreCriterion.Statement := by
  intro A _ hA
  refine ⟨fun h => ⟨fun P _ hdim => ?_, fun P _ => ?_⟩, fun h => hN A hA h.1 h.2⟩
  · obtain ⟨hd, hi⟩ := h P
    exact isRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_le_one _ (by exact_mod_cast hdim)
  · obtain ⟨hd, hi⟩ := h P
    exact hS _

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
