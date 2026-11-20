import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumMulCosetRepresentativeTraceEq
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSumMulCosetRepresentativeTraceEq.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.sum_mul_cosetRepresentativeTrace_eq : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] (N : Subgroup G) [Fintype (G ⧸ N)] (n : ℕ) (a b : Fin n → L) (c : L), IsSep v N a b c → ∀ x ∈ Fix L N, ∑ i, a i * cosetTrace N (b i * x) = c * x := by
  first | exact @GlobalTheory.AlmostEt.sum_mul_cosetTrace_eq | exact GlobalTheory.AlmostEt.sum_mul_cosetTrace_eq | (intros; apply GlobalTheory.AlmostEt.sum_mul_cosetTrace_eq <;> assumption)
