import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMemSpanLinearRoots
import Mathlib
import Formalism.DegreeFormula.FlagDegFormula
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PowLinSpan.span_pow_linRoot` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHomogeneousMemSpanLinearRoots.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.homogeneous_mem_span_linear_roots : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N d : ℕ) (Q : MvPolynomial (ι × Fin N) ℝ), Q.IsHomogeneous d →
    Q ∈ Submodule.span ℝ ((fun u => Formalism.DegreeFormula.linRoot u ^ d) '' {u : ι → Fin N → ℝ | ∀ τ, StrictAnti (u τ)}) := by
  first | exact @GlobalTheory.PowLinSpan.span_pow_linRoot | exact GlobalTheory.PowLinSpan.span_pow_linRoot | (intros; apply GlobalTheory.PowLinSpan.span_pow_linRoot <;> assumption)
