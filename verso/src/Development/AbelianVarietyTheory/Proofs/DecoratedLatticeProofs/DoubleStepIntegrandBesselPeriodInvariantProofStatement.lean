import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandBesselPeriodInvariantProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FDoubleStepIntegrandBesselPeriodInvariantProof.lean&line=291#L291)
-/
theorem _root_.GlobalTheory.T.doubleStepIntegrandBesselPeriodInvariant_proof : ∀ D : D7, GlobalTheory.FinPl.HandInv D := by
  first | exact @GlobalTheory.FinPl.HandInvPf.handInv | exact GlobalTheory.FinPl.HandInvPf.handInv | (intros; apply GlobalTheory.FinPl.HandInvPf.handInv <;> assumption)
