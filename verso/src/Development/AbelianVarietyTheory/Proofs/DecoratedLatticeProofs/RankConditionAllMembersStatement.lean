import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RankConditionAllMembers
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Fam.MemberCount.member_rankMu` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FRankConditionAllMembers.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.rank_condition_all_members : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => ∀ u, GlobalTheory.Core.Rk.RankMu D u) := by
  first | exact @GlobalTheory.Fam.MemberCount.member_rankMu | exact GlobalTheory.Fam.MemberCount.member_rankMu | (intros; apply GlobalTheory.Fam.MemberCount.member_rankMu <;> assumption)
