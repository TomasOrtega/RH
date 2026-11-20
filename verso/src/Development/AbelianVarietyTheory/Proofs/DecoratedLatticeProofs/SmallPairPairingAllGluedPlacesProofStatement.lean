import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAllGluedPlacesProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.FinPl.SmallAllPf.main | exact GlobalTheory.FinPl.SmallAllPf.main | (intros; apply GlobalTheory.FinPl.SmallAllPf.main <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.smallPairPairingAllGluedPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.SmallAll D := by
  first | exact @GlobalTheory.FinPl.SmallAllPf.main | exact GlobalTheory.FinPl.SmallAllPf.main | (intros; apply GlobalTheory.FinPl.SmallAllPf.main <;> assumption)
