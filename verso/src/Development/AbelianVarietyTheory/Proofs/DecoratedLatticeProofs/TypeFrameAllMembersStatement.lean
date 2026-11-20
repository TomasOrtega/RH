import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeFrameAllMembers
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Fam.MemberFrame.member_tFrameAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FTypeFrameAllMembers.lean&line=151#L151)
-/
theorem _root_.GlobalTheory.T.type_frame_all_members : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => Formalism.L2.SG.RowsConc.TFrameAt D) := by
  first | exact @GlobalTheory.Fam.MemberFrame.member_tFrameAt | exact GlobalTheory.Fam.MemberFrame.member_tFrameAt | (intros; apply GlobalTheory.Fam.MemberFrame.member_tFrameAt <;> assumption)
