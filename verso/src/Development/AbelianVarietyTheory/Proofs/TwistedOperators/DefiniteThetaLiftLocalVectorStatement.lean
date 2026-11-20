import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteThetaLiftLocalVector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AdjVecLocal.thetaVecLocal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FDefiniteThetaLiftLocalVector.lean&line=323#L323)
-/
theorem _root_.GlobalTheory.T.definiteThetaLift_localVector : ∀ D : D7, ThetaVecLocal D := by
  first | exact @GlobalTheory.AdjVecLocal.thetaVecLocal | exact GlobalTheory.AdjVecLocal.thetaVecLocal | (intros; apply GlobalTheory.AdjVecLocal.thetaVecLocal <;> assumption)
