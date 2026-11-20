import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LargeGapAllMembers
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Core.Rk.GapAt.rowE_bigGap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FLargeGapAllMembers.lean&line=132#L132)
-/
theorem _root_.GlobalTheory.T.large_gap_all_members : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => GlobalTheory.Core.Rk.BigGap D) := by
  first | exact @GlobalTheory.Core.Rk.GapAt.rowE_bigGap | exact GlobalTheory.Core.Rk.GapAt.rowE_bigGap | (intros; apply GlobalTheory.Core.Rk.GapAt.rowE_bigGap <;> assumption)
