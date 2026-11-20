import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchOfWeilRepresentation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.fourierMatch_of_weil` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FJacquetRallisFourierMatchOfWeilRepresentation.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.jacquetRallisFourierMatch_of_weilRepresentation : WeilEt → RankOne → GammaOne → ∀ r, FourierMatch r := by
  first | exact @GlobalTheory.JR.fourierMatch_of_weil | exact GlobalTheory.JR.fourierMatch_of_weil | (intros; apply GlobalTheory.JR.fourierMatch_of_weil <;> assumption)
