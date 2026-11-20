import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.DiscreteSeriesUpqUnique

namespace GlobalTheory.CompanionTheory.Front

/- English proof (translation)
The claim follows from `GlobalTheory.Published.discreteSeriesHermitianUnique_iff.2 discreteSeriesUpqUnique`.
-/
theorem discreteSeriesHermitianUnique : GlobalTheory.Published.DiscreteSeriesHermitianUnique :=
  GlobalTheory.Published.discreteSeriesHermitianUnique_iff.2 discreteSeriesUpqUnique

end GlobalTheory.CompanionTheory.Front
