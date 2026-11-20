import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAverageTwistedSpanEqZero
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCharacterAverageTwistedSpanEqZero.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.character_average_twistedSpan_eq_zero : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ → ∀ u ∈ aug π H θ, ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ j ∈ R, j ∈ H) ∧ ∑ j ∈ R, (θ j)⁻¹ • π j u = 0 := by
  first | exact @GlobalTheory.PsType.aug_avg_zero | exact GlobalTheory.PsType.aug_avg_zero | (intros; apply GlobalTheory.PsType.aug_avg_zero <;> assumption)
