import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityNeZeroSubquotient
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FJacquetMultiplicityNeZeroSubquotient.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.jacquet_multiplicity_ne_zero_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), Zc.jm x hd π ≠ 0 → ∃ S T : Subrepresentation (jac (stdBlocks (fun a => (x a).1) hd) π), Nonempty ((subQuot S T).Equiv (piTensor fun a => (x a).rep)) := by
  first | exact @GlobalTheory.CompanionTheory.JmSub.exists_subQuot_of_jm_ne_zero | exact GlobalTheory.CompanionTheory.JmSub.exists_subQuot_of_jm_ne_zero | (intros; apply GlobalTheory.CompanionTheory.JmSub.exists_subQuot_of_jm_ne_zero <;> assumption)
