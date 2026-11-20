import Development.WeilBound.CoreStatements.RegularisedThetaMirabolic.CuspidalMirabolic.CuspidalRestrictsToInduced
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIrreducibleTransportRep

namespace PositivityTheory.Mirab

/- English proof (translation)
Assemble the required witnesses or components as `⟨GlobalTheory.CompanionTheory.Hypotheses₂.cuspidalExists_holds, PositivityTheory.Mirab.Restr.cuspidalRestrictsToInduced⟩`.
-/
theorem cuspidalMirabolic : GlobalTheory.Published.CuspidalMirabolic :=
  ⟨GlobalTheory.CompanionTheory.Hypotheses₂.cuspidalExists_holds, PositivityTheory.Mirab.Restr.cuspidalRestrictsToInduced⟩

end PositivityTheory.Mirab
