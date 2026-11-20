import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorConjugateTangentSpacePadZeroColumns
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FTaylorConjugateTangentSpacePadZeroColumns.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.taylorConjugate_tangentSpacePadZeroColumns : ∀ (D : D7) (N N' m : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (G : VC D (N + m) N' → ℂ), Differentiable ℂ G → fnConj D M ρ (fun z : VC D N N' => G (pad D m z)) = fun z => fnConj D M ρ G (pad D m z) := by
  first | exact @GlobalTheory.ConjRestrict.fnConj_pad | exact GlobalTheory.ConjRestrict.fnConj_pad | (intros; apply GlobalTheory.ConjRestrict.fnConj_pad <;> assumption)
