import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KappaNormAtSplitPrimes
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FKappaNormAtSplitPrimes.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.kappa_norm_at_splitPrimes : ∀ D : D7, KappaSplit D := by
  first | exact @GlobalTheory.kappaSplit_all | exact GlobalTheory.kappaSplit_all | (intros; apply GlobalTheory.kappaSplit_all <;> assumption)
