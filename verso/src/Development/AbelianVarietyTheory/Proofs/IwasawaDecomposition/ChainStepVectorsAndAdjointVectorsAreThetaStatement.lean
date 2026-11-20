import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepVectorsAndAdjointVectorsAreTheta
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.StepVecThetaLem
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.VecTheta.vecThetaSD | exact GlobalTheory.VecTheta.vecThetaSD | (intros; apply GlobalTheory.VecTheta.vecThetaSD <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.chainStepVectors_and_adjointVectors_areTheta : ∀ D : D7, Formalism.IndefR.Fin.VecThetaSD D := by
  first | exact @GlobalTheory.VecTheta.vecThetaSD | exact GlobalTheory.VecTheta.vecThetaSD | (intros; apply GlobalTheory.VecTheta.vecThetaSD <;> assumption)
