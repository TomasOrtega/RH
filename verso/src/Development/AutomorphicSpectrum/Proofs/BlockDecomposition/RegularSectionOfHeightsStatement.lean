import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSectionOfHeights
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RSecPf.rSec_of_htExist` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRegularSectionOfHeights.lean&line=309#L309)
-/
theorem _root_.GlobalTheory.T.regular_section_of_heights : HtExist → RSec := by
  first | exact @GlobalTheory.CompanionTheory.RSecPf.rSec_of_htExist | exact GlobalTheory.CompanionTheory.RSecPf.rSec_of_htExist | (intros; apply GlobalTheory.CompanionTheory.RSecPf.rSec_of_htExist <;> assumption)
