import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedPlaceSourceConstantProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinPl.sourceExact` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FGluedPlaceSourceConstantProof.lean&line=185#L185)
-/
theorem _root_.GlobalTheory.T.gluedPlaceSourceConstant_proof : ∀ D : D7, GlobalTheory.FinPl.SourceExact D := by
  first | exact @GlobalTheory.FinPl.sourceExact | exact GlobalTheory.FinPl.sourceExact | (intros; apply GlobalTheory.FinPl.sourceExact <;> assumption)
