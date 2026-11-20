import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness

namespace GlobalTheory

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness`.
-/
theorem bernsteinZelevinskyFiniteness_holds : GlobalTheory.Published.BernsteinZelevinskyFiniteness :=
  GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness

end GlobalTheory
