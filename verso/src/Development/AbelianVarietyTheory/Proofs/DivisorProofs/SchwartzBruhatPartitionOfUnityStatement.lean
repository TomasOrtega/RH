import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartitionOfUnity
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemNsp
open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CoverSB.mem_span_of_cover` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzBruhatPartitionOfUnity.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.schwartzBruhat_partition_of_unity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ι : Type) [Finite ι] (U : ι → Set (Matrix A D k)), (∀ i, IsOpen (U i)) → ∀ f ∈ SB (Matrix A D k), (∀ Y, f Y ≠ 0 → ∃ i, Y ∈ U i) → f ∈ Submodule.span ℂ {g | g ∈ SB (Matrix A D k) ∧ ∃ i, ∀ Y, g Y ≠ 0 → Y ∈ U i} := by
  first | exact @GlobalTheory.CoverSB.mem_span_of_cover | exact GlobalTheory.CoverSB.mem_span_of_cover | (intros; apply GlobalTheory.CoverSB.mem_span_of_cover <;> assumption)
