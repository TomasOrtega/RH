import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnThetaKernelDefiniteSeesawStage
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SqTower.integrableOn_ker'_of_stage_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegrableOnThetaKernelDefiniteSeesawStage.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.integrableOn_thetaKernel_definiteSeesawStage : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) (p : ℕ)
    (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p 0 X →
    ∀ (t : T) (P' : PolF D WW.rank A'.rank) (h : GA D WW), MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m' := by
  first | exact @GlobalTheory.SqTower.integrableOn_ker'_of_stage_zero | exact GlobalTheory.SqTower.integrableOn_ker'_of_stage_zero | (intros; apply GlobalTheory.SqTower.integrableOn_ker'_of_stage_zero <;> assumption)
