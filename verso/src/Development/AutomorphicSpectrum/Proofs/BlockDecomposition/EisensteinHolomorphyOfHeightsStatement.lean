import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHolomorphyOfHeights
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.EisHolFam.eisHol_of_htExist` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEisensteinHolomorphyOfHeights.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.eisenstein_holomorphy_of_heights : HtExist → EisHol := by
  first | exact @GlobalTheory.CompanionTheory.EisHolFam.eisHol_of_htExist | exact GlobalTheory.CompanionTheory.EisHolFam.eisHol_of_htExist | (intros; apply GlobalTheory.CompanionTheory.EisHolFam.eisHol_of_htExist <;> assumption)
