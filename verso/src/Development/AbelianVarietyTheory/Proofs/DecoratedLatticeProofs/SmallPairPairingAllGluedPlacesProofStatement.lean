import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAllGluedPlacesProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSmallPairPairingAllGluedPlacesProof.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.smallPairPairingAllGluedPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.SmallAll D := by
  first | exact @GlobalTheory.FinPl.SmallAllPf.main | exact GlobalTheory.FinPl.SmallAllPf.main | (intros; apply GlobalTheory.FinPl.SmallAllPf.main <;> assumption)
