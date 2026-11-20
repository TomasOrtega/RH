import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealDerivativeFockVectorsAll
import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.WeilReal.realAllO | exact GlobalTheory.WeilReal.realAllO | (intros; apply GlobalTheory.WeilReal.realAllO <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.weilDatum_realDerivative_fockVectors_all : ∀ D : D7, Formalism.IndefR.WeilFull.RealAllO D := by
  first | exact @GlobalTheory.WeilReal.realAllO | exact GlobalTheory.WeilReal.realAllO | (intros; apply GlobalTheory.WeilReal.realAllO <;> assumption)
