import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepSmallPairsValueAllGluedSplitPlacesProo
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FDoubleStepSmallPairsValueAllGluedSplitPlacesProo.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.doubleStepSmallPairsValueAllGluedSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.VertexAll D := by
  first | exact @GlobalTheory.FinPl.vertexAll | exact GlobalTheory.FinPl.vertexAll | (intros; apply GlobalTheory.FinPl.vertexAll <;> assumption)
