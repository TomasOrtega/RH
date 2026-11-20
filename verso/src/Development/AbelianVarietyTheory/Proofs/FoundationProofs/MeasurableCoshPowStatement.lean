import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableCoshPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FMeasurableCoshPow.lean&line=119#L119)
-/
theorem _root_.GlobalTheory.T.measurable_coshPow' : ∀ (p q : ℕ) (c : ℝ), Measurable (coshPow c : UpqT p q → ℝ) := by
  first | exact @GlobalTheory.CoshPowMeas.measurable_coshPow | exact GlobalTheory.CoshPowMeas.measurable_coshPow | (intros; apply GlobalTheory.CoshPowMeas.measurable_coshPow <;> assumption)
