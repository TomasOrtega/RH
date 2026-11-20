import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterWeightMap
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit
open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCharacterWeightMap.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.character_weight_map : ChWMap := by
  first | exact @GlobalTheory.CompanionTheory.CharInf.chWMap | exact GlobalTheory.CompanionTheory.CharInf.chWMap | (intros; apply GlobalTheory.CompanionTheory.CharInf.chWMap <;> assumption)
