import CompanionTheory.AutomorphicTheory.MirabolicRestriction.MirabolicInduction.CuspidalRestrictsToInduced
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIrreducibleTransportRep

namespace CompanionTheory.Mirab

/- English proof (translation)
Assemble the required witnesses or components as `⟨GlobalTheory.CompanionTheory.Hypotheses₂.cuspidalExists_holds, CompanionTheory.Mirab.Restr.cuspidalRestrictsToInduced⟩`.
-/
theorem cuspidalMirabolic : GlobalTheory.Published.CuspidalMirabolic :=
  ⟨GlobalTheory.CompanionTheory.Hypotheses₂.cuspidalExists_holds, CompanionTheory.Mirab.Restr.cuspidalRestrictsToInduced⟩

end CompanionTheory.Mirab
