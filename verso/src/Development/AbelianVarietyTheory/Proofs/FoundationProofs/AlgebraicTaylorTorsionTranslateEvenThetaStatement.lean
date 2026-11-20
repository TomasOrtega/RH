import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorTorsionTranslateEvenTheta
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FAlgebraicTaylorTorsionTranslateEvenTheta.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.algebraicTaylor_torsionTranslate_evenTheta : ∀ Λ : AddSubgroup ℂ, IsLat Λ → (∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (sgStar Λ))) → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (GL3Theta.th0 Λ t₀)) ∧ ∀ ω ∈ Λ, ∃ κ ∈ Qbar, κ ≠ 0 ∧ ∀ z, U1 Λ (x + ω) (GL3Theta.th0 Λ t₀) z = κ * U1 Λ x (GL3Theta.th0 Λ t₀) z := by
  first | exact @GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt | exact GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt | (intros; apply GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt <;> assumption)
