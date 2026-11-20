import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FrobJm.one_le_jm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FJacquetMultiplicityPos.lean&line=173#L173)
-/
theorem _root_.GlobalTheory.T.jacquet_multiplicity_pos : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin N) k) V), IsSmooth τ → ∀ f : τ.IntertwiningMap (prodIrr x hd), (∃ v, f v ≠ 0) → 1 ≤ jm x hd τ := by
  first | exact @GlobalTheory.CompanionTheory.FrobJm.one_le_jm | exact GlobalTheory.CompanionTheory.FrobJm.one_le_jm | (intros; apply GlobalTheory.CompanionTheory.FrobJm.one_le_jm <;> assumption)
