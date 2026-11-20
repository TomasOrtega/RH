import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

/- English proof (translation)
Introduce `K f c s`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Establish `hex : ∃ c, ∀ᶠ m in Filter.atTop, f m = c` using `⟨c, h⟩`. Rewrite using `[eventualValue, dif_pos hex]`. Take `⟨m, hm1, hm2⟩` from `(hex.choose_spec.and h).exists`.

Conclude with `hm1.symm.trans hm2`. Establish `ht : Filter.Tendsto (fun m : K → ℤ => m - s) Filter.atTop Filter.atTop`. Rewrite using `[Filter.tendsto_atTop_atTop]`. Introduce `b`. Use `⟨b + s, fun a ha => ?_⟩` and prove the remaining obligations.

Simplify using `using sub_le_sub_right ha s`. Conclude with `ht.eventually h`.
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
