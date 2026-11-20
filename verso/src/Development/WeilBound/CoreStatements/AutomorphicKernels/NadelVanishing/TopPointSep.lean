import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointSeparationPairOfPrincipalisation
import Development.WeilBound.CoreStatements.ResolutionCharZero.PrincipalisationClosed

namespace NadelVanishingSeparation.NSI

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pointSeparationPair : GlobalTheory.Published.PointSeparationPair :=
  GlobalTheory.pointSeparationPair_of_principalisation PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed

end NadelVanishingSeparation.NSI
