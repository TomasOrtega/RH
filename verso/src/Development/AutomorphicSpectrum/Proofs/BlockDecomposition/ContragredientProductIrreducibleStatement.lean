import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FContragredientProductIrreducible.lean&line=188#L188)
-/
theorem _root_.GlobalTheory.T.contragredient_product_irreducible : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), ∃ hd' : ∑ a, (dualCl (x a)).1 = N, Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr (fun a => dualCl (x a)) hd')) := by
  first | exact @GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr | exact GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr | (intros; apply GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr <;> assumption)
