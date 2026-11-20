import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstMaximalMinor
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RankFibreKer.exists_isFirstMax` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFirstMaximalMinor.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_first_maximal_minor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k), (∃ J, minor Y J ≠ 0) → ∃ J, IsFirstMax Y J := by
  first | exact @GlobalTheory.RankFibreKer.exists_isFirstMax | exact GlobalTheory.RankFibreKer.exists_isFirstMax | (intros; apply GlobalTheory.RankFibreKer.exists_isFirstMax <;> assumption)
