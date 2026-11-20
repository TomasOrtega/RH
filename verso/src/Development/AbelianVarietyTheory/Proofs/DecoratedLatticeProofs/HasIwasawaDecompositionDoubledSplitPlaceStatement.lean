import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Core.Rk.IwSplit.hasIwasawa_split` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FHasIwasawaDecompositionDoubledSplitPlace.lean&line=127#L127)
-/
theorem _root_.GlobalTheory.T.hasIwasawaDecomposition_doubled_split_place : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ v : FinPl D, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → HasIwasawa D.sp.cm.sig (dblSp A).gram (KFin D.sp.cm.sig (dblSp A).gram L v) := by
  first | exact @GlobalTheory.Core.Rk.IwSplit.hasIwasawa_split | exact GlobalTheory.Core.Rk.IwSplit.hasIwasawa_split | (intros; apply GlobalTheory.Core.Rk.IwSplit.hasIwasawa_split <;> assumption)
