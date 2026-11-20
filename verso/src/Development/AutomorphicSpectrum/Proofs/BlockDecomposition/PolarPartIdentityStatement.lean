import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPolarPartIdentity.lean&line=268#L268)
-/
theorem _root_.GlobalTheory.T.polar_part_identity : MapsExist → HtExist → HeckeEta → RightId → PoleReal → FJEis → PcBound → RSec → EisHol → ThTotal → CfFJ → PcFc → SphBound → Polar := by
  first | exact @GlobalTheory.CompanionTheory.RswPolar.polar | exact GlobalTheory.CompanionTheory.RswPolar.polar | (intros; apply GlobalTheory.CompanionTheory.RswPolar.polar <;> assumption)
