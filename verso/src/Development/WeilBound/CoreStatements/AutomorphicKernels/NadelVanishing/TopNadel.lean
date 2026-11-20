import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.NadelVanishingPairsOfPrincipalisation
import Development.WeilBound.CoreStatements.ResolutionCharZero.PrincipalisationClosed

namespace NadelVanishingSeparation.NSI

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nadelVanishingPair : GlobalTheory.Published.NadelVanishingPair :=
  GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed

end NadelVanishingSeparation.NSI
