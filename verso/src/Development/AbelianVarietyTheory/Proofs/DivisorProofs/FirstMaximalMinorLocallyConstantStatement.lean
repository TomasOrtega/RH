import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstMaximalMinorLocallyConstant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RankFibreKer.isFirstMax_eventually` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFirstMaximalMinorLocallyConstant.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.first_maximal_minor_locally_constant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d), IsFirstMax Y J →
    ∀ᶠ Y' in nhds Y, IsFirstMax Y' J := by
  first | exact @GlobalTheory.RankFibreKer.isFirstMax_eventually | exact GlobalTheory.RankFibreKer.isFirstMax_eventually | (intros; apply GlobalTheory.RankFibreKer.isFirstMax_eventually <;> assumption)
