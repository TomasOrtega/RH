import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.StepVecThetaLem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt

open Formalism.BasicNotions

namespace GlobalTheory.VecTheta

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem vecThetaSD : ∀ D : D7, Formalism.IndefR.Fin.VecThetaSD D := fun _ =>
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => isThetaFunO_stepVec h,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => isThetaFunO_thPVec h⟩

end GlobalTheory.VecTheta
