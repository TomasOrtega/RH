import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepSplitIntertwiner
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SegQuotTwo.quottwo` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSegmentRepSplitIntertwiner.lean&line=135#L135)
-/
theorem _root_.GlobalTheory.T.segment_rep_split_intertwiner : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsLSeg Δ π) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len) (u v : IrrGL k) (hu : IsLSeg (segLow Δ a h0) u.rep) (hv : IsLSeg (segHigh Δ a h1) v.rep) (hd : ∑ i, (![u, v] i).1 = N), ∃ f : (prodIrr ![u, v] hd).IntertwiningMap π, Function.Surjective f := by
  first | exact @GlobalTheory.CompanionTheory.SegQuotTwo.quottwo | exact GlobalTheory.CompanionTheory.SegQuotTwo.quottwo | (intros; apply GlobalTheory.CompanionTheory.SegQuotTwo.quottwo <;> assumption)
