import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerCosetRepresentativeTraceEqOfLtOne
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AlmostEt.exists_integer_coset_trace_eq'` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsIntegerCosetRepresentativeTraceEqOfLtOne.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.exists_integer_cosetRepresentativeTrace_eq_of_lt_one : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (U : Subgroup G) [Fintype (G ⧸ U)], AlmostSep v U → ∀ e : L, (∀ g : G, g • e = e) → v e < 1 → ∃ y ∈ Fix L U, v y ≤ 1 ∧ cosetTrace U y = e := by
  first | exact @GlobalTheory.AlmostEt.exists_integer_coset_trace_eq' | exact GlobalTheory.AlmostEt.exists_integer_coset_trace_eq' | (intros; apply GlobalTheory.AlmostEt.exists_integer_coset_trace_eq' <;> assumption)
