import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchingOfWeilField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FJacquetRallisFourierMatchingOfWeilField.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.jacquetRallis_fourier_matching_of_weil_field : WeilField → ∀ r, FourierMatch r := by
  first | exact @GlobalTheory.JR.fourierMatch_of_weilField | exact GlobalTheory.JR.fourierMatch_of_weilField | (intros; apply GlobalTheory.JR.fourierMatch_of_weilField <;> assumption)
