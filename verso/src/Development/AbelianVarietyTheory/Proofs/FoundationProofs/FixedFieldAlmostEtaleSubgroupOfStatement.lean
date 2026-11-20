import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedFieldAlmostEtaleSubgroupOf
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FFixedFieldAlmostEtaleSubgroupOf.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.fixedFieldAlmostEtale_subgroupOf : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] (U H : Subgroup G), AlmostSep v U → AlmostSep v (U.subgroupOf H) := by
  first | exact @GlobalTheory.AlmostEt.almostSep_subgroupOf | exact GlobalTheory.AlmostEt.almostSep_subgroupOf | (intros; apply GlobalTheory.AlmostEt.almostSep_subgroupOf <;> assumption)
