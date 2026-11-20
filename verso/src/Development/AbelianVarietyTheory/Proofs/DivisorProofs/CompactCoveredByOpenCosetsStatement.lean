import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCoveredByOpenCosets
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.compact_finite_leftCoset_reps` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCompactCoveredByOpenCosets.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.compact_covered_by_open_cosets : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    ∀ C : Set G, IsCompact C →
    ∃ R : Finset G, (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') ∧ ∀ g ∈ C, ∃ r ∈ R, r⁻¹ * g ∈ K := by
  first | exact @GlobalTheory.compact_finite_leftCoset_reps | exact GlobalTheory.compact_finite_leftCoset_reps | (intros; apply GlobalTheory.compact_finite_leftCoset_reps <;> assumption)
