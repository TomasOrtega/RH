import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightIdentityStatement
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Dblock.rightId` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRightIdentityStatement.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.right_identity_statement : RightId := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.rightId | exact GlobalTheory.CompanionTheory.Dblock.rightId | (intros; apply GlobalTheory.CompanionTheory.Dblock.rightId <;> assumption)
