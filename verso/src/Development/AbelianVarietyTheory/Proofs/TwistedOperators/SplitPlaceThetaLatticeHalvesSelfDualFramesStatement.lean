import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceThetaLatticeHalvesSelfDualFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SplitLatticeHalves.splitLattice` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FSplitPlaceThetaLatticeHalvesSelfDualFrames.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.splitPlace_thetaLattice_halves_selfDual_frames : ∀ D : D7, SplitLattice D := by
  first | exact @GlobalTheory.SplitLatticeHalves.splitLattice | exact GlobalTheory.SplitLatticeHalves.splitLattice | (intros; apply GlobalTheory.SplitLatticeHalves.splitLattice <;> assumption)
