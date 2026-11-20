import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepVectorsAndAdjointVectorsAreTheta
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.StepVecThetaLem
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FChainStepVectorsAndAdjointVectorsAreTheta.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.chainStepVectors_and_adjointVectors_areTheta : ∀ D : D7, Formalism.IndefR.Fin.VecThetaSD D := by
  first | exact @GlobalTheory.VecTheta.vecThetaSD | exact GlobalTheory.VecTheta.vecThetaSD | (intros; apply GlobalTheory.VecTheta.vecThetaSD <;> assumption)
