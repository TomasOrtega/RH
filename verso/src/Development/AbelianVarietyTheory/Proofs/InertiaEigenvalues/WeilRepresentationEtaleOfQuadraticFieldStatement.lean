import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationEtaleOfQuadraticField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWeilRepresentationEtaleOfQuadraticField.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.weilRepresentationEtale_of_quadraticField : WeilField → WeilEt := by
  first | exact @GlobalTheory.JR.weilEt_of_weilField | exact GlobalTheory.JR.weilEt_of_weilField | (intros; apply GlobalTheory.JR.weilEt_of_weilField <;> assumption)
