import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Size.sizeBasic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSizeBasicOfConjPlaces.lean&line=214#L214)
-/
theorem _root_.GlobalTheory.T.size_basic_of_conj_places : SzFin → ConjPlaces → SizeBasic := by
  first | exact @GlobalTheory.CompanionTheory.Size.sizeBasic | exact GlobalTheory.CompanionTheory.Size.sizeBasic | (intros; apply GlobalTheory.CompanionTheory.Size.sizeBasic <;> assumption)
