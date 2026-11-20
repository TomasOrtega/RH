import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoleReality
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PoleBound.poleReal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPoleReality.lean&line=139#L139)
-/
theorem _root_.GlobalTheory.T.pole_reality : PoleReal := by
  first | exact @GlobalTheory.CompanionTheory.PoleBound.poleReal | exact GlobalTheory.CompanionTheory.PoleBound.poleReal | (intros; apply GlobalTheory.CompanionTheory.PoleBound.poleReal <;> assumption)
