import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterExistsUnique
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistedIndependenceLemma.TwistedIndependence
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHeckeCharacterExistsUnique.lean&line=259#L259)
-/
theorem _root_.GlobalTheory.T.hecke_character_exists_unique : PositivityTheory.Lbc.HeckeExistsUnique := by
  first | exact @GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique | exact GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique | (intros; apply GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique <;> assumption)
