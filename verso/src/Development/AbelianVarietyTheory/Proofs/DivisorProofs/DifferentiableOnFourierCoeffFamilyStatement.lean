import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnFourierCoeffFamily
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableExpNegL1Norm
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TauPeriod Complex
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.differentiableOn_cf_fibre_of_holomorphic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDifferentiableOnFourierCoeffFamily.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.differentiableOn_fourier_coeff_family : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} {U : Set E} (a : Pt E g → ℂ), IsOpen U → DifferentiableOn ℂ a (cov U g) → ∀ n : Fin g → ℤ, DifferentiableOn ℂ (fun b => cf (fun z => a (b, z)) n) U := by
  first | exact @GlobalTheory.differentiableOn_cf_fibre_of_holomorphic | exact GlobalTheory.differentiableOn_cf_fibre_of_holomorphic | (intros; apply GlobalTheory.differentiableOn_cf_fibre_of_holomorphic <;> assumption)
