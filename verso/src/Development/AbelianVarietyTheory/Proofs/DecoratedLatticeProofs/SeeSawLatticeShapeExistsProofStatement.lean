import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLatticeShapeExistsProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSeeSawLatticeShapeExistsProof.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.seeSawLatticeShapeExists_proof : ∀ D : D7, GlobalTheory.SeeSaw.ShapeEx D := by
  first | exact @GlobalTheory.SeeSaw.ShapeExProof.shapeEx | exact GlobalTheory.SeeSaw.ShapeExProof.shapeEx | (intros; apply GlobalTheory.SeeSaw.ShapeExProof.shapeEx <;> assumption)
