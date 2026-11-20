import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeArcHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FConeArcHolds.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.cone_arc_holds : ConeArcSt := by
  first | exact @GlobalTheory.ConeArc.coneArc | exact GlobalTheory.ConeArc.coneArc | (intros; apply GlobalTheory.ConeArc.coneArc <;> assumption)
