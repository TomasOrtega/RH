import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SourceLiftAtGluedPlaceProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.FinPl.sourceGlued | exact GlobalTheory.FinPl.sourceGlued | (intros; apply GlobalTheory.FinPl.sourceGlued <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.sourceLiftAtGluedPlace_proof : ∀ D : D7, GlobalTheory.FinPl.SourceGlued D := by
  first | exact @GlobalTheory.FinPl.sourceGlued | exact GlobalTheory.FinPl.sourceGlued | (intros; apply GlobalTheory.FinPl.sourceGlued <;> assumption)
