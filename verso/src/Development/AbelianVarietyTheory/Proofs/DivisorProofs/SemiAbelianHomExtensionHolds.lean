import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.ImportsAlt

namespace GlobalTheory

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.SAH.semiAbelianHomExtension`.
-/
theorem semiAbelianHomExtension_holds : GlobalTheory.Published.SemiAbelianHomExtension :=
  GlobalTheory.CompanionTheory.SAH.semiAbelianHomExtension

end GlobalTheory
