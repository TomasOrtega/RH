import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesAlgebraicConstant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5 Polynomial
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.laurentSeries_eq_C_of_root` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FLaurentSeriesAlgebraicConstant.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.laurent_series_algebraic_constant : ∀ (k : Type) [Field k] (f : LaurentSeries k), (∃ P : k[X], P ≠ 0 ∧ eval₂ HahnSeries.C f P = 0) → ∃ c : k, f = HahnSeries.C c := by
  first | exact @GlobalTheory.laurentSeries_eq_C_of_root | exact GlobalTheory.laurentSeries_eq_C_of_root | (intros; apply GlobalTheory.laurentSeries_eq_C_of_root <;> assumption)
