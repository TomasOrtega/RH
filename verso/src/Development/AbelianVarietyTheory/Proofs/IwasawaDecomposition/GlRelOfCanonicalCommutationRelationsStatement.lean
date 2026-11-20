import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlRelOfCanonicalCommutationRelations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
open Matrix GlobalTheory.Mem.Lift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.Lift.glRel_of_isCCR` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FGlRelOfCanonicalCommutationRelations.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.glRel_of_canonicalCommutationRelations : ∀ (A : Type) [Ring A] (n m : ℕ) (x d : Fin n × Fin m → A), IsCCR x d → Formalism.REAL.GlRel (fun i j : Fin n => ∑ a, x (i, a) * d (j, a)) ∧ Formalism.REAL.GlRel (fun a b : Fin m => -∑ i, x (i, b) * d (i, a)) := by
  first | exact @GlobalTheory.Mem.Lift.glRel_of_isCCR | exact GlobalTheory.Mem.Lift.glRel_of_isCCR | (intros; apply GlobalTheory.Mem.Lift.glRel_of_isCCR <;> assumption)
