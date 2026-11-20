import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MahlerBoundOfDegree
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Cutoff.mahler_of` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMahlerBoundOfDegree.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.mahler_bound_of_degree : DegBdd → DegRat → MahlerC → Mahler := by
  first | exact @GlobalTheory.CompanionTheory.Cutoff.mahler_of | exact GlobalTheory.CompanionTheory.Cutoff.mahler_of | (intros; apply GlobalTheory.CompanionTheory.Cutoff.mahler_of <;> assumption)
