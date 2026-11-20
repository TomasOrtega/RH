import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem EventualValueFacts.proof : EventualValueFacts.Statement := by
  intro K f c s
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hex : ∃ c, ∀ᶠ m in Filter.atTop, f m = c := ⟨c, h⟩
    rw [eventualValue, dif_pos hex]
    obtain ⟨m, hm1, hm2⟩ := (hex.choose_spec.and h).exists
    exact hm1.symm.trans hm2
  · have ht : Filter.Tendsto (fun m : K → ℤ => m - s) Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      refine ⟨b + s, fun a ha => ?_⟩
      simpa using sub_le_sub_right ha s
    exact ht.eventually h

end GroundTheory.Heights₂.Heights.NumbersDVR
