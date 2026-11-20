import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness

namespace GlobalTheory.Laid

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem bzfin_holds : GlobalTheory.Published.BernsteinZelevinskyFiniteness := by
  intro k _ _ _ _

  exact ⟨CompanionTheory.SmGLBridge.irreducibleAdmissible k, CompanionTheory.JacquetBridge.jacquetFiniteLength k,
    CompanionTheory.BZInd.inductionFiniteLength k, SmGL.IndDual.inductionContragredient k⟩

end GlobalTheory.Laid
