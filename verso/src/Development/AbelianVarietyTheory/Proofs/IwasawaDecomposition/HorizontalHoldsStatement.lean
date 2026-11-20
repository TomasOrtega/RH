import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FHorizontalHolds.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.horizontal_holds : HorizSt := by
  first | exact @GlobalTheory.HorizProof.horizSt | exact GlobalTheory.HorizProof.horizSt | (intros; apply GlobalTheory.HorizProof.horizSt <;> assumption)
