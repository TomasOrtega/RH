import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealDerivativeFockVectorsAll
import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FWeilDatumRealDerivativeFockVectorsAll.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.weilDatum_realDerivative_fockVectors_all : ∀ D : D7, Formalism.IndefR.WeilFull.RealAllO D := by
  first | exact @GlobalTheory.WeilReal.realAllO | exact GlobalTheory.WeilReal.realAllO | (intros; apply GlobalTheory.WeilReal.realAllO <;> assumption)
