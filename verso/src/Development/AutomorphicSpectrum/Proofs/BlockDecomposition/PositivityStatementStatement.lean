import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositivityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Jp.Pos.jpPos` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPositivityStatement.lean&line=393#L393)
-/
theorem _root_.GlobalTheory.T.positivity_statement : GlobalTheory.CompanionTheory.Jp.JpPos := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Pos.jpPos | exact GlobalTheory.CompanionTheory.Jp.Pos.jpPos | (intros; apply GlobalTheory.CompanionTheory.Jp.Pos.jpPos <;> assumption)
