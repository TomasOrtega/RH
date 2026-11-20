import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsClassificationOrderFreeEquiv
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LUniq.isL_unique` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLanglandsClassificationOrderFreeEquiv.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.langlands_classification_order_free_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LOrderFree k → ∀ (𝔭 : Multiset (Segment k)) {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W), IsL 𝔭 π → IsL 𝔭 σ → Nonempty (π.Equiv σ) := by
  first | exact @GlobalTheory.CompanionTheory.LUniq.isL_unique | exact GlobalTheory.CompanionTheory.LUniq.isL_unique | (intros; apply GlobalTheory.CompanionTheory.LUniq.isL_unique <;> assumption)
