import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsInterleaveSum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ZcMerge.exists_common_orderedForm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FOrderedFormsInterleaveSum.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.ordered_forms_interleave_sum : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)), ∃ (h₁ h₂ h : ℕ) (Δ₁ : Fin h₁ → Segment k) (Δ₂ : Fin h₂ → Segment k) (Δ : Fin h → Segment k), IsOrderedForm Δ₁ 𝔪 ∧ IsOrderedForm Δ₂ 𝔫 ∧ IsOrderedForm Δ (𝔪 + 𝔫) ∧ Zc.Comb.Interleave (wtW Δ₁) (wtW Δ₂) (wtW Δ) := by
  first | exact @GlobalTheory.CompanionTheory.ZcMerge.exists_common_orderedForm | exact GlobalTheory.CompanionTheory.ZcMerge.exists_common_orderedForm | (intros; apply GlobalTheory.CompanionTheory.ZcMerge.exists_common_orderedForm <;> assumption)
