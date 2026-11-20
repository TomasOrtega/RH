import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolatedNonKltDivisorOfPrincipalisation
import Development.WeilBound.CoreStatements.ResolutionCharZero.PrincipalisationClosed

namespace NadelVanishingSeparation.NSI

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isolatedNonKltDivisor : GlobalTheory.Published.IsolatedNonKltDivisor :=
  GlobalTheory.isolatedNonKltDivisor_of_principalisation PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed

end NadelVanishingSeparation.NSI
