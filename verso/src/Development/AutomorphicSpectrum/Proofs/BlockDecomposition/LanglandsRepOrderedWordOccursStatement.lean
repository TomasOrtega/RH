import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsRepOrderedWordOccurs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLanglandsRepOrderedWordOccurs.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.langlands_rep_ordered_word_occurs : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → ∀ (𝔪 : Multiset (Segment k)) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsL 𝔪 π → ∀ (h : ℕ) (Δ : Fin h → Segment k), IsOrderedForm Δ 𝔪 → Wd π (wtW Δ) := by
  first | exact @GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL | exact GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL | (intros; apply GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL <;> assumption)
