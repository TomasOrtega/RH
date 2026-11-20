import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreRadicalAway
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreRadical
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RadicalAwayRabinowitsch
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Introduce `σ _ n K g hK`. Take `⟨F, hF0, hF⟩` from `hR σ (Option (Fin n)) (rabinowitschIdeal K g) ((isRadicalAway_iff_isRadical_rabinowitschIdeal K g).1 hK)`. Use `⟨F, hF0, fun t ht => ?_⟩` and prove the remaining obligations. Establish `h` using `hF t ht`. Rewrite `h` using `[rabinowitschIdeal_map]`.

Conclude with `(isRadicalAway_iff_isRadical_rabinowitschIdeal (fibreIdeal K t) _).2 h`.
-/
theorem GenericFibreRadicalAway.proof (hR : GenericFibreRadical.Statement) :
    GenericFibreRadicalAway.Statement := by
  intro σ _ n K g hK
  obtain ⟨F, hF0, hF⟩ := hR σ (Option (Fin n)) (rabinowitschIdeal K g)
    ((isRadicalAway_iff_isRadical_rabinowitschIdeal K g).1 hK)
  refine ⟨F, hF0, fun t ht => ?_⟩
  have h := hF t ht
  rw [rabinowitschIdeal_map] at h
  exact (isRadicalAway_iff_isRadical_rabinowitschIdeal (fibreIdeal K t) _).2 h

end

end GroundTheory.Heights₂.Heights
