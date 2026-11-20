import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LexSumSplitFirstBlockStrictMono
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.lexSumSplit_strictMono` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FLexSumSplitFirstBlockStrictMono.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.lexSum_splitFirstBlock_strictMono : ∀ (s : ℕ) (t : Fin (s + 1) → ℕ), StrictMono fun c : Fin (t 0) ⊕ₗ (Σₗ i : Fin s, Fin (t i.succ)) => (Sum.elim (fun j => toLex (⟨0, j⟩ : Σ a, Fin (t a))) (fun x => toLex (⟨(ofLex x).1.succ, (ofLex x).2⟩ : Σ a, Fin (t a))) (ofLex c) : Σₗ a, Fin (t a)) := by
  first | exact @GlobalTheory.lexSumSplit_strictMono | exact GlobalTheory.lexSumSplit_strictMono | (intros; apply GlobalTheory.lexSumSplit_strictMono <;> assumption)
