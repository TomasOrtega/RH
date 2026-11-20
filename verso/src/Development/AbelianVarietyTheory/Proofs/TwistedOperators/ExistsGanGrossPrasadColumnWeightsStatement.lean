import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGanGrossPrasadColumnWeights
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsGanGrossPrasadColumnWeights.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.exists_ganGrossPrasad_column_weights : ∀ (S : Sizes) (Q : Entries S), Q.Good → ∃ kap : ∀ i : Fin (S.m + 1), DomWeight (S.nC i), (∀ r, (kap 0).dual.w r = hw Q.basePar r) ∧ (∀ r, (kap (Fin.last _)).dual.w r = hw Q.smallPar r) ∧ ∀ i : Fin S.m, StepW (Q.c i.rev - ((S.nC i.succ + 1) / 2 : ℕ)) (-Q.c i.rev + ((S.nC i.castSucc + 1) / 2 : ℕ)) (kap i.castSucc) (kap i.succ) := by
  first | exact @GlobalTheory.OneFunctional.ColumnWeights.exists_column_weights | exact GlobalTheory.OneFunctional.ColumnWeights.exists_column_weights | (intros; apply GlobalTheory.OneFunctional.ColumnWeights.exists_column_weights <;> assumption)
