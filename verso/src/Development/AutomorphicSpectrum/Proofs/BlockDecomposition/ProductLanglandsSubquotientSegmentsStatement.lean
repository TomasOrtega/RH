import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductLanglandsSubquotientSegments
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FProductLanglandsSubquotientSegments.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.product_langlands_subquotient_segments : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)) (a b : IrrGL k), IsL 𝔪 a.rep → IsL 𝔫 b.rep → ∃ (h : ℕ) (z : Fin h → IrrGL k) (Δ : Fin h → Segment k) (hd : ∑ i, (z i).1 = a.1 + b.1), (∀ i, IsLSeg (Δ i) (z i).rep) ∧ Finset.univ.val.map Δ = 𝔪 + 𝔫 ∧ IsSubquotient (prod₂ a.rep b.rep) (prodIrr z hd) := by
  first | exact @GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg | exact GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg | (intros; apply GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg <;> assumption)
