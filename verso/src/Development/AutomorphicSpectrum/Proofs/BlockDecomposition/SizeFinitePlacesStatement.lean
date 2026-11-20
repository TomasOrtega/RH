import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeFinitePlaces
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSizeFinitePlaces.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.size_finite_places : SzFin := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin | exact GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin | (intros; apply GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin <;> assumption)
