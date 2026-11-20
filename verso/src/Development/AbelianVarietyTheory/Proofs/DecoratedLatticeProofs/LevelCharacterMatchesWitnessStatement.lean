import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterMatchesWitness
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FLevelCharacterMatchesWitness.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.chrEq_mu0_of_bWit : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → ∀ j : Fin q.B.R.m, Formalism.IndefR.Links.ChrEq ((pk (packB b)).mu0 ((j : ℕ) + 1)) (q.w.I.C.mu0 j) := by
  first | exact @GlobalTheory.Fam.level_character_matches_witness | exact GlobalTheory.Fam.level_character_matches_witness | (intros; apply GlobalTheory.Fam.level_character_matches_witness <;> assumption)
