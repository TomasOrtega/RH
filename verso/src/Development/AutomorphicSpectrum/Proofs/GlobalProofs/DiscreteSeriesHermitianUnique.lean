import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.DiscreteSeriesUpqUnique

namespace GlobalTheory.CompanionTheory.Front

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem discreteSeriesHermitianUnique : GlobalTheory.Published.DiscreteSeriesHermitianUnique :=
  GlobalTheory.Published.discreteSeriesHermitianUnique_iff.2 discreteSeriesUpqUnique

end GlobalTheory.CompanionTheory.Front
