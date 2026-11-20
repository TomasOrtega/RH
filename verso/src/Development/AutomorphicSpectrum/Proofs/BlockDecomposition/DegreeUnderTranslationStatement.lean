import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeUnderTranslation
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.DegMoveProof.degMove_of` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDegreeUnderTranslation.lean&line=163#L163)
-/
theorem _root_.GlobalTheory.T.degree_under_translation : MulF → MulI → SzFin → FinSupp → DegBasisG → DegMove := by
  first | exact @GlobalTheory.CompanionTheory.DegMoveProof.degMove_of | exact GlobalTheory.CompanionTheory.DegMoveProof.degMove_of | (intros; apply GlobalTheory.CompanionTheory.DegMoveProof.degMove_of <;> assumption)
