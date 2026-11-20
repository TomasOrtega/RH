import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DecoratedLatticeOfAdelicMatrixEqRowPoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FDecoratedLatticeOfAdelicMatrixEqRowPoint.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.decoratedLatticeOfAdelicMatrix_eq_rowPoint : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X), I.Ok → ∀ (a : I.ι) (y : GlobalTheory.Mem.Col2.TC.GA B (B.R.N B.R.m - 1)) (p : GlobalTheory.Mem.Col2.XPt (B.primes X) B.R I.sel (I.tup a)), GlobalTheory.Mem.Col2.TC.PtOf y p → GlobalTheory.TopVal.latOf I a y = GlobalTheory.Mem.Col2.toRow I.sel (I.tup a) p := by
  first | exact @GlobalTheory.TopVal.DecoPt.latOf_eq_toRow | exact GlobalTheory.TopVal.DecoPt.latOf_eq_toRow | (intros; apply GlobalTheory.TopVal.DecoPt.latOf_eq_toRow <;> assumption)
