import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominationHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DomModels.domSt_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FDominationHolds.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.domination_holds : DomSt := by
  first | exact @GlobalTheory.DomModels.domSt_holds | exact GlobalTheory.DomModels.domSt_holds | (intros; apply GlobalTheory.DomModels.domSt_holds <;> assumption)
