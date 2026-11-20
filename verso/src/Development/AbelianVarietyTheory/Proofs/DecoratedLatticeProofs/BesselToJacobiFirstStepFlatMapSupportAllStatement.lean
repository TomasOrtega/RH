import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFirstStepFlatMapSupportAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinPl.suppFirst_all` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FBesselToJacobiFirstStepFlatMapSupportAll.lean&line=117#L117)
-/
theorem _root_.GlobalTheory.T.besselToJacobiFirstStepFlatMapSupport_all : ∀ D : D7, GlobalTheory.FinPl.SuppFirst D := by
  first | exact @GlobalTheory.FinPl.suppFirst_all | exact GlobalTheory.FinPl.suppFirst_all | (intros; apply GlobalTheory.FinPl.suppFirst_all <;> assumption)
