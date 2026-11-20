import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationQuadraticFieldExists
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWeilRepresentationQuadraticFieldExists.lean&line=189#L189)
-/
theorem _root_.GlobalTheory.T.weilRepresentation_quadraticField_exists : WeilField := by
  first | exact @GlobalTheory.JR.WeilQuad.weilField_main | exact GlobalTheory.JR.WeilQuad.weilField_main | (intros; apply GlobalTheory.JR.WeilQuad.weilField_main <;> assumption)
