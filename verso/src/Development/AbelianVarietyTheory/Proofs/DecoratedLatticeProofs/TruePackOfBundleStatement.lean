import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TruePackOfBundle
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Fam.truePack_of_bWit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FTruePackOfBundle.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.true_pack_of_bundle : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → Nonempty (Bl.RXs q.x.what₂) → PtRows b → TruePack (packB b) := by
  first | exact @GlobalTheory.Fam.truePack_of_bWit | exact GlobalTheory.Fam.truePack_of_bWit | (intros; apply GlobalTheory.Fam.truePack_of_bWit <;> assumption)
