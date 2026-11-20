import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceLatticeStabilisersFixWeilVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PlaceTensor.splitVacuumFixed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FSplitPlaceLatticeStabilisersFixWeilVacuum.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.splitPlace_latticeStabilisers_fix_weilVacuum : ∀ D : D7, SplitVacuumFixed D := by
  first | exact @GlobalTheory.PlaceTensor.splitVacuumFixed | exact GlobalTheory.PlaceTensor.splitVacuumFixed | (intros; apply GlobalTheory.PlaceTensor.splitVacuumFixed <;> assumption)
