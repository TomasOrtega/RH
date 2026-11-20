import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCartanInvolutionOrthDecBlockSumRealMat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumMatApply
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Core.Rk.SumBox.isCartanInv_sumMat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FIsCartanInvolutionOrthDecBlockSumRealMat.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.isCartanInvolution_orthDecBlockSumRealMat : ∀ (D : D7) (B W H : HSp D) (o : OrthDec B W H) (sW : RealMat W) (sH : RealMat H), (∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → ∀ τ, IsCartanInv (gramAt D B τ) (sumMat o sW sH τ) := by
  first | exact @GlobalTheory.Core.Rk.SumBox.isCartanInv_sumMat | exact GlobalTheory.Core.Rk.SumBox.isCartanInv_sumMat | (intros; apply GlobalTheory.Core.Rk.SumBox.isCartanInv_sumMat <;> assumption)
