import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RadicalSubspaceFacts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RadicalForm.radical` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRadicalSubspaceFacts.lean&line=155#L155)
-/
theorem _root_.GlobalTheory.T.radical_subspace_facts : Radical := by
  first | exact @GlobalTheory.CompanionTheory.RadicalForm.radical | exact GlobalTheory.CompanionTheory.RadicalForm.radical | (intros; apply GlobalTheory.CompanionTheory.RadicalForm.radical <;> assumption)
