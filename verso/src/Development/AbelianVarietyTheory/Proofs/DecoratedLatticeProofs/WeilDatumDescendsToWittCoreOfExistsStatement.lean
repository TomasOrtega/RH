import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCoreOfExists
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Unf.descent_of_weilDatumExists` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FWeilDatumDescendsToWittCoreOfExists.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.weilDatumDescendsToWittCore_of_exists : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion.WeilDatumExists D → Descent D := by
  first | exact @GlobalTheory.Unf.descent_of_weilDatumExists | exact GlobalTheory.Unf.descent_of_weilDatumExists | (intros; apply GlobalTheory.Unf.descent_of_weilDatumExists <;> assumption)
