import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPureTensors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FockPureTensor.fockPure` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFockVectorsPureTensors.lean&line=204#L204)
-/
theorem _root_.GlobalTheory.T.fockVectors_pureTensors : ∀ D : D7, FockPure D := by
  first | exact @GlobalTheory.FockPureTensor.fockPure | exact GlobalTheory.FockPureTensor.fockPure | (intros; apply GlobalTheory.FockPureTensor.fockPure <;> assumption)
