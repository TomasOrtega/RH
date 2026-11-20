import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelTrueOfWitness
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Fam.BundleLev.levTrue_packB` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FLevelTrueOfWitness.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.level_true_of_witness : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → LevTrue (packB b) := by
  first | exact @GlobalTheory.Fam.BundleLev.levTrue_packB | exact GlobalTheory.Fam.BundleLev.levTrue_packB | (intros; apply GlobalTheory.Fam.BundleLev.levTrue_packB <;> assumption)
