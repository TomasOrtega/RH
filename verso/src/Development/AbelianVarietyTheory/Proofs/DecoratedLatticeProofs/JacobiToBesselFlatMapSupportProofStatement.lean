import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FJacobiToBesselFlatMapSupportProof.lean&line=578#L578)
-/
theorem _root_.GlobalTheory.T.jacobiToBesselFlatMapSupport_proof : ∀ D : D7, GlobalTheory.FinPl.SupportShift D := by
  first | exact @GlobalTheory.FinPl.supportShift | exact GlobalTheory.FinPl.supportShift | (intros; apply GlobalTheory.FinPl.supportShift <;> assumption)
