import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumAtSplitPlacesProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LastTAllPf.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FLastSeeSawDatumAtSplitPlacesProof.lean&line=246#L246)
-/
theorem _root_.GlobalTheory.T.lastSeeSawDatumAtSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.LastTAll D := by
  first | exact @GlobalTheory.LastTAllPf.main | exact GlobalTheory.LastTAllPf.main | (intros; apply GlobalTheory.LastTAllPf.main <;> assumption)
