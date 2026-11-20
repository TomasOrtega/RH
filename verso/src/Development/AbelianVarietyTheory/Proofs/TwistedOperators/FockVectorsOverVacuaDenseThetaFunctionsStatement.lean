import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FockDensity.fockDense` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFockVectorsOverVacuaDenseThetaFunctions.lean&line=448#L448)
-/
theorem _root_.GlobalTheory.T.fockVectors_overVacua_dense_thetaFunctions : ∀ D : D7, GlobalTheory.ChainFr.FockDense D := by
  first | exact @GlobalTheory.FockDensity.fockDense | exact GlobalTheory.FockDensity.fockDense | (intros; apply GlobalTheory.FockDensity.fockDense <;> assumption)
