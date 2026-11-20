import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleFiniteCoeffTendstoAndBounded
import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultipliableTpFactor
open Complex
open scoped Real
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FJacobiTripleFiniteCoeffTendstoAndBounded.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.jacobiTripleFiniteCoeff_tendsto_and_bounded : ∀ t : ℂ, ‖t‖ < 1 → (∀ j : ℤ, Filter.Tendsto (fun n : ℕ => GlobalTheory.JacobiTriple.finCoeff t n j) Filter.atTop (nhds (GlobalTheory.JacobiTriple.qPochInf t)⁻¹)) ∧ ∃ C : ℝ, ∀ (n : ℕ) (j : ℤ), ‖GlobalTheory.JacobiTriple.finCoeff t n j‖ ≤ C := by
  first | exact @GlobalTheory.JacobiTriple.finCoeff_tendsto_and_bounded | exact GlobalTheory.JacobiTriple.finCoeff_tendsto_and_bounded | (intros; apply GlobalTheory.JacobiTriple.finCoeff_tendsto_and_bounded <;> assumption)
