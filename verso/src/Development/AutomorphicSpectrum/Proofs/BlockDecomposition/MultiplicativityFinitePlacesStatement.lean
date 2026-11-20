import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityFinitePlaces
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
open Matrix PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.WedgeMinor.mulF` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMultiplicativityFinitePlaces.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.multiplicativity_finite_places : MulF := by
  first | exact @GlobalTheory.CompanionTheory.WedgeMinor.mulF | exact GlobalTheory.CompanionTheory.WedgeMinor.mulF | (intros; apply GlobalTheory.CompanionTheory.WedgeMinor.mulF <;> assumption)
