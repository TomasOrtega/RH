import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistCharacterMatchesWitness
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FTwistCharacterMatchesWitness.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.twist_character_matches_witness : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → ∀ t, Formalism.IndefR.Links.ChrEq ((pk (packB b)).xi t) (q.w.I.xi (b.P.I.tup t)) := by
  first | exact @GlobalTheory.Fam.xi_chrEq_cols | exact GlobalTheory.Fam.xi_chrEq_cols | (intros; apply GlobalTheory.Fam.xi_chrEq_cols <;> assumption)
