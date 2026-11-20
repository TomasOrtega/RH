import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodEvaluationUnfoldingOfWittDescent
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
Apply `GlobalTheory.Unf.evalBF_of_descent` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FBesselPeriodEvaluationUnfoldingOfWittDescent.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.bessel_period_evaluation_unfolding_of_witt_descent : ∀ D : D7, Descent D → EvalBF D := by
  first | exact @GlobalTheory.Unf.evalBF_of_descent | exact GlobalTheory.Unf.evalBF_of_descent | (intros; apply GlobalTheory.Unf.evalBF_of_descent <;> assumption)
