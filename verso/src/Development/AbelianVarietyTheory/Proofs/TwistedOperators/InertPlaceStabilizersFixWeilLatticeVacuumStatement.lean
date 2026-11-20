import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceStabilizersFixWeilLatticeVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FInertPlaceStabilizersFixWeilLatticeVacuum.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.inert_place_stabilizers_fix_weil_lattice_vacuum : ∀ D : D7, InertVacuumFixed D := by
  first | exact @GlobalTheory.PlaceTensor.inertVacuumFixed | exact GlobalTheory.PlaceTensor.inertVacuumFixed | (intros; apply GlobalTheory.PlaceTensor.inertVacuumFixed <;> assumption)
