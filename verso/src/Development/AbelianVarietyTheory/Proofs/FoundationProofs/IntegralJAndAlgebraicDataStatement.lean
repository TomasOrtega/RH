import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FIntegralJAndAlgebraicData.lean&line=126#L126)
-/
theorem _root_.GlobalTheory.T.admJ_and_torsion_data_algebraic : ∀ (D : D7), admG1 D → GL3Theta.admJ D ∧ ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → DataIn D (tor0 D cc δ) Qbar ∧ ∀ t, InRationalLattice (lamOf D cc δ) t → t ∉ (lamOf D cc δ) → wpF (lamOf D cc δ) t ∈ Qbar ∧ wpD (lamOf D cc δ) t ∈ Qbar := by
  first | exact @GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data | exact GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data | (intros; apply GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data <;> assumption)
