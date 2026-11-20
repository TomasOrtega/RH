import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSocleOfMultiplicityOne.lean&line=172#L172)
-/
theorem _root_.GlobalTheory.T.socle_of_multiplicity_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), jm x hd (prodIrr x hd) ≤ 1 → ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one | exact GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one | (intros; apply GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one <;> assumption)
