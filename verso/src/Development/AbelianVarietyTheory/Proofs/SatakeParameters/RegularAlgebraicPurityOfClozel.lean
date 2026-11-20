import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelPurity
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.RegularAlgebraicPurity

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem regularAlgebraicPurity_of_clozel (hP : GlobalTheory.Published.ClozelPurity) (hC : GlobalTheory.Published.ClozelCohomological) :
    GlobalTheory.Published.RegularAlgebraicPurity := by
  intro E _ _ _ a ha π hr
  exact ⟨hP E a ha π fun τ => (hr τ).2, hC E a ha π hr⟩

end GlobalTheory
