import Development.WeilBound.CoreStatements.RegularisedThetaMirabolic.CuspidalMirabolic.CuspidalRestrictsToInduced
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIrreducibleTransportRep

namespace PositivityTheory.Mirab

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem cuspidalMirabolic : GlobalTheory.Published.CuspidalMirabolic :=
  ⟨GlobalTheory.CompanionTheory.Hypotheses₂.cuspidalExists_holds, PositivityTheory.Mirab.Restr.cuspidalRestrictsToInduced⟩

end PositivityTheory.Mirab
