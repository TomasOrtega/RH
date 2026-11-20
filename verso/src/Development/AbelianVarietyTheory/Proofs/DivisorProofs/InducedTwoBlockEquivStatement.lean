import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedTwoBlockEquiv
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IndEq.indSp_equiv_indAA` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FInducedTwoBlockEquiv.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.induced_two_block_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a a' : ℕ) (α β : kˣ →* ℂˣ), ∃ e : GlobalTheory.KSplit.indSp a a' α β ≃ₗ[ℂ] IndAA k a a' ![α, β], ∀ f x, (e f).1.1 x = (f : GL (Fin (a + a')) k → ℂ) x := by
  first | exact @GlobalTheory.IndEq.indSp_equiv_indAA | exact GlobalTheory.IndEq.indSp_equiv_indAA | (intros; apply GlobalTheory.IndEq.indSp_equiv_indAA <;> assumption)
