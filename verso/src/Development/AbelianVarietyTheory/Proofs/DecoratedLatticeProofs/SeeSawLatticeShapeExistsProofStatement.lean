import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLatticeShapeExistsProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.SeeSaw.ShapeExProof.shapeEx | exact GlobalTheory.SeeSaw.ShapeExProof.shapeEx | (intros; apply GlobalTheory.SeeSaw.ShapeExProof.shapeEx <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.seeSawLatticeShapeExists_proof : ∀ D : D7, GlobalTheory.SeeSaw.ShapeEx D := by
  first | exact @GlobalTheory.SeeSaw.ShapeExProof.shapeEx | exact GlobalTheory.SeeSaw.ShapeExProof.shapeEx | (intros; apply GlobalTheory.SeeSaw.ShapeExProof.shapeEx <;> assumption)
