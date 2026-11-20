import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedWordLettersCuspidal
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FOrderedWordLettersCuspidal.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.ordered_word_letters_cuspidal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Δ : Fin h → Segment k), ∀ c ∈ wtW Δ, c.IsCusp := by
  first | exact @GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp | exact GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp | (intros; apply GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp <;> assumption)
