import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneMajorant
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRankOneMajorant.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.rank_one_majorant : WeilCont → WeilKFin → OrbitMaj → IwaCpt → FockTranslateSchwartzMajorant := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.rank_one_majorant_of_parts | exact GlobalTheory.CompanionTheory.ThTot.rank_one_majorant_of_parts | (intros; apply GlobalTheory.CompanionTheory.ThTot.rank_one_majorant_of_parts <;> assumption)
