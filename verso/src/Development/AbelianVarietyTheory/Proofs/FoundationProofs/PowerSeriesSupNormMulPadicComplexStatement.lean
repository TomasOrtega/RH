import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesSupNormMulPadicComplex
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FPowerSeriesSupNormMulPadicComplex.lean&line=145#L145)
-/
theorem _root_.GlobalTheory.T.powerSeries_supNorm_mul_padicComplex : ∀ (p : ℕ) [Fact p.Prime] (f g : PowerSeries ℂ_[p]) (c : ℝ), BddSer f → BddSer g → (∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ c) → ∀ i j, ‖PowerSeries.coeff i f‖ * ‖PowerSeries.coeff j g‖ ≤ c := by
  first | exact @GlobalTheory.EvenTheta.sup_norm_mul_padicComplex | exact GlobalTheory.EvenTheta.sup_norm_mul_padicComplex | (intros; apply GlobalTheory.EvenTheta.sup_norm_mul_padicComplex <;> assumption)
