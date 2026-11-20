import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStable
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFockPolynomialVectorsOfSmoothThetaStable.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.fockPolynomialVectors_of_smoothTheta_stable : ∀ D : D7, Formalism.IndefR.Fin.PtStable D := by
  first | exact @GlobalTheory.FockTheta.ptStable | exact GlobalTheory.FockTheta.ptStable | (intros; apply GlobalTheory.FockTheta.ptStable <;> assumption)
