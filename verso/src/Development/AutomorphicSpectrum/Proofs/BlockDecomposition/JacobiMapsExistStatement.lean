import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FJacobiMapsExist.lean&line=349#L349)
-/
theorem _root_.GlobalTheory.T.jacobi_maps_exist : MapsExist := by
  first | exact @GlobalTheory.CompanionTheory.JacobiMaps.mapsExist | exact GlobalTheory.CompanionTheory.JacobiMaps.mapsExist | (intros; apply GlobalTheory.CompanionTheory.JacobiMaps.mapsExist <;> assumption)
