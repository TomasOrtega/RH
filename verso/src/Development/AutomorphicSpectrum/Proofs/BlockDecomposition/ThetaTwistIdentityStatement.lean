import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTwistIdentity
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FThetaTwistIdentity.lean&line=369#L369)
-/
theorem _root_.GlobalTheory.T.theta_twist_identity : ThTwist := by
  first | exact @GlobalTheory.CompanionTheory.ThTw.thTwist | exact GlobalTheory.CompanionTheory.ThTw.thTwist | (intros; apply GlobalTheory.CompanionTheory.ThTw.thTwist <;> assumption)
