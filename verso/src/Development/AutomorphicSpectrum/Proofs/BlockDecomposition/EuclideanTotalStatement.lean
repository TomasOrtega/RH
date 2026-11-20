import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EuclideanTotal
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEuclideanTotal.lean&line=239#L239)
-/
theorem _root_.GlobalTheory.T.euclidean_total : EucTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.EucT.eucTotal | exact GlobalTheory.CompanionTheory.ThTot.EucT.eucTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.EucT.eucTotal <;> assumption)
