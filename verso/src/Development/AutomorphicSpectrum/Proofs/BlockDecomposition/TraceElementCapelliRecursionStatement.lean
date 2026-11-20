import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementCapelliRecursion
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CapelliEigen.etr_apply_of_eigen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTraceElementCapelliRecursion.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.trace_element_capelli_recursion : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V), Formalism.REAL.GlRel E → ∀ (P : Polynomial ℂ) (v : V), (∀ u : ℂ, Formalism.REAL.qdet E u v = P.eval u • v) → ∀ (N : ℕ) (t : ℕ → ℂ), (∀ k < N, Formalism.REAL.etr E k v = t k • v) → Formalism.REAL.etr E N v = ((-1 : Polynomial ℂ) ^ N * ((Polynomial.X - Polynomial.C (m : ℂ)) ^ (N + 1) * ((P).comp (Polynomial.X + 1) - (P)) - (P) * ∑ k ∈ Finset.range N, Polynomial.C ((-1) ^ k * t k) * (Polynomial.X - Polynomial.C (m : ℂ)) ^ (N - k))).coeff (m + 1) • v := by
  first | exact @GlobalTheory.CompanionTheory.CapelliEigen.etr_apply_of_eigen | exact GlobalTheory.CompanionTheory.CapelliEigen.etr_apply_of_eigen | (intros; apply GlobalTheory.CompanionTheory.CapelliEigen.etr_apply_of_eigen <;> assumption)
