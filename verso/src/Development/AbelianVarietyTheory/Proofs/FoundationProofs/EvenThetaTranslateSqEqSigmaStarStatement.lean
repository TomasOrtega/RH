import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTranslateSqEqSigmaStar
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FEvenThetaTranslateSqEqSigmaStar.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.U1_sq_mul_U1_th0_sq_eq_sgStar : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ t, t ∉ Λ → ∀ z, U1 Λ t (sgStar Λ) 0 ^ 2 * U1 Λ t (GL3Theta.th0 Λ t₀) z ^ 2 = -(U1 Λ (2 * t) (sgStar Λ) z * sgStar Λ z) + (wpF Λ t - wpF Λ t₀) * U1 Λ t (sgStar Λ) 0 ^ 2 * U1 Λ t (sgStar Λ) z ^ 2 := by
  first | exact @GlobalTheory.EvenTheta.IsLat.evenTheta_translate_sq_eq_sigmaStar | exact GlobalTheory.EvenTheta.IsLat.evenTheta_translate_sq_eq_sigmaStar | (intros; apply GlobalTheory.EvenTheta.IsLat.evenTheta_translate_sq_eq_sigmaStar <;> assumption)
