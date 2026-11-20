import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSpanSchwartzBruhatProductEqTop.lean&line=149#L149)
-/
theorem _root_.GlobalTheory.T.span_schwartzBruhatProduct_eq_top : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y], Submodule.span ℂ (Set.range fun q : SB X × SB Y => prodSB q.1 q.2) = ⊤ := by
  first | exact @GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top | exact GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top | (intros; apply GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top <;> assumption)
