import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConstantsExistForBundle
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FConstantsExistForBundle.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.constants_exist_for_bundle : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL) (F G H : ℝ → ℝ → ℝ), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D O _ _ => ∃ C' Cl Cg CT : ℝ, F Cg CT ≤ C' ∧ G Cg CT ≤ Cl ∧ H Cg CT ≤ O.L.sc.L ∧ GlobalTheory.Core.Rk.HD D O.L.sc.L C' Cl Cg (1 / 4) 3 (1 / 2) CT ∧ GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D O.L.sc.L C' ∧ (∀ u, GlobalTheory.Core.Rk.RankMu D u) ∧ GlobalTheory.Core.Rk.BigGap D ∧ 1 ≤ D.R.rS) := by
  first | exact @GlobalTheory.Fam.MemberSizes.member_sizes | exact GlobalTheory.Fam.MemberSizes.member_sizes | (intros; apply GlobalTheory.Fam.MemberSizes.member_sizes <;> assumption)
