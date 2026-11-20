import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubSegmentProduct
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SegUniq.isLSeg_of_dec` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIrreducibleSubSegmentProduct.lean&line=117#L117)
-/
theorem _root_.GlobalTheory.T.irreducible_sub_segment_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) (Δ : Segment k) {N : ℕ} (hd : ∑ a, (dec Δ a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth τ) (hi : τ.IsIrreducible) (f : τ.IntertwiningMap (prodIrr (dec Δ) hd)) (hf : Function.Injective f), IsLSeg Δ τ := by
  first | exact @GlobalTheory.CompanionTheory.SegUniq.isLSeg_of_dec | exact GlobalTheory.CompanionTheory.SegUniq.isLSeg_of_dec | (intros; apply GlobalTheory.CompanionTheory.SegUniq.isLSeg_of_dec <;> assumption)
