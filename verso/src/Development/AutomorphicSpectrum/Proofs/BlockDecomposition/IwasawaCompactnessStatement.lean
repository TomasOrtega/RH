import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCompactness
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIwasawaCompactness.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.iwasawa_compactness : IwaCpt := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.iwaCpt | exact GlobalTheory.CompanionTheory.ThTot.iwaCpt | (intros; apply GlobalTheory.CompanionTheory.ThTot.iwaCpt <;> assumption)
