import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceStabilizerTrivial
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RankFibreKer.eq_one_of_mem_slice_of_mul_mem_slice` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSliceStabilizerTrivial.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.slice_stabilizer_trivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice k a d → g.val * Z ∈ slice k a d → g = 1 := by
  first | exact @GlobalTheory.RankFibreKer.eq_one_of_mem_slice_of_mul_mem_slice | exact GlobalTheory.RankFibreKer.eq_one_of_mem_slice_of_mul_mem_slice | (intros; apply GlobalTheory.RankFibreKer.eq_one_of_mem_slice_of_mul_mem_slice <;> assumption)
