import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CovariantVectorToFunctionFormCoeffMemRange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReprMemOfCoeff
open Formalism.L2.DIV MvPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FCovariantVectorToFunctionFormCoeffMemRange.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.covariantVectorToFunctionForm_coeff_mem_range : ∀ {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L] (κ : L →+* ℂ), GlobalTheory.FunObj.ReadOK σ → ∀ (F : VV ℂ σ), (∀ m, MvPolynomial.coeff m F.1 ∈ Set.range κ) → ∀ m, MvPolynomial.coeff m (GlobalTheory.FunObj.funOf σ F).1 ∈ Set.range κ := by
  first | exact @GlobalTheory.RowFun.coeff_funOf_mem_range | exact GlobalTheory.RowFun.coeff_funOf_mem_range | (intros; apply GlobalTheory.RowFun.coeff_funOf_mem_range <;> assumption)
