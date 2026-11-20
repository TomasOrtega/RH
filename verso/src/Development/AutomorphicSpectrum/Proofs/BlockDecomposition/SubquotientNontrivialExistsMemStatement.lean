import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientNontrivialExistsMem
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SubQuotNe.exists_mem_not_mem_of_subQuot_equiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSubquotientNontrivialExistsMem.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.subquotient_nontrivial_exists_mem : ∀ {M W X : Type} [Group M] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ M W) (σ : Representation ℂ M X) (S T : Subrepresentation ρ), Nonempty ((subQuot S T).Equiv σ) → Nontrivial X → ∃ s ∈ S.toSubmodule, s ∉ T.toSubmodule := by
  first | exact @GlobalTheory.CompanionTheory.SubQuotNe.exists_mem_not_mem_of_subQuot_equiv | exact GlobalTheory.CompanionTheory.SubQuotNe.exists_mem_not_mem_of_subQuot_equiv | (intros; apply GlobalTheory.CompanionTheory.SubQuotNe.exists_mem_not_mem_of_subQuot_equiv <;> assumption)
