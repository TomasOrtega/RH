import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.DixmierMalliavin.DixmierMalliavinFactorisationHolds

namespace GlobalTheory

/- English proof (translation)
The claim follows from `CompanionTheory.DM.dixmierMalliavinFactorisation_holds`.
-/
theorem dixmierMalliavinFactorisation_fromLibrary : GlobalTheory.Published.DixmierMalliavinFactorisation :=
  CompanionTheory.DM.dixmierMalliavinFactorisation_holds

end GlobalTheory
