import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteAdeleExtendedCharacterOfCurve
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinWeil.AdelicChar.exists_psi` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsFiniteAdeleExtendedCharacterOfCurve.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.exists_finiteAdeleExtendedCharacter_of_curve : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ ψ : AE D → ℂ, IsPsi D cc δ ψ := by
  first | exact @GlobalTheory.FinWeil.AdelicChar.exists_psi | exact GlobalTheory.FinWeil.AdelicChar.exists_psi | (intros; apply GlobalTheory.FinWeil.AdelicChar.exists_psi <;> assumption)
