import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTotalOfEuclidean
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ThTot.fockTotal_of_eucTotal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFockTotalOfEuclidean.lean&line=265#L265)
-/
theorem _root_.GlobalTheory.T.fock_total_of_euclidean : EucTotal → FockTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.fockTotal_of_eucTotal | exact GlobalTheory.CompanionTheory.ThTot.fockTotal_of_eucTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.fockTotal_of_eucTotal <;> assumption)
