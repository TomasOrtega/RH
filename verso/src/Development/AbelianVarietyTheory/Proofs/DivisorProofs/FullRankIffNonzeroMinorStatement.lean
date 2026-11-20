import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankIffNonzeroMinor
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFullRankIffNonzeroMinor.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.full_rank_iff_nonzero_minor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k), Y.rank = a ↔ ∃ J, minor Y J ≠ 0 := by
  first | exact @GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero | exact GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero | (intros; apply GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero <;> assumption)
