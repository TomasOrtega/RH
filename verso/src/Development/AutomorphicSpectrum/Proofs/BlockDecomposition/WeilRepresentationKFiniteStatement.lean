import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationKFinite
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ThTot.weilKFin` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWeilRepresentationKFinite.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.weil_representation_K_finite : WeilKFin := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.weilKFin | exact GlobalTheory.CompanionTheory.ThTot.weilKFin | (intros; apply GlobalTheory.CompanionTheory.ThTot.weilKFin <;> assumption)
