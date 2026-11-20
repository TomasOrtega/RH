import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSocleSegmentProduct
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsSocleSegmentProduct.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.exists_socle_segment_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} (hd : ∑ a, (dec Δ a).1 = N), ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr (dec Δ) hd) := by
  first | exact @GlobalTheory.CompanionTheory.SegSocle.exists_isSocle_prodIrr_dec | exact GlobalTheory.CompanionTheory.SegSocle.exists_isSocle_prodIrr_dec | (intros; apply GlobalTheory.CompanionTheory.SegSocle.exists_isSocle_prodIrr_dec <;> assumption)
