import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationContinuity
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ThTot.weilCont` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWeilRepresentationContinuity.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.weil_representation_continuity : WeilCont := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.weilCont | exact GlobalTheory.CompanionTheory.ThTot.weilCont | (intros; apply GlobalTheory.CompanionTheory.ThTot.weilCont <;> assumption)
