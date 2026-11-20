import Mathlib
import Formalism.GelfandTransference.Statement
import Lemmata.DetNormLeProdRows.DetNormLeProdRows

open Matrix Finset
open scoped ComplexOrder

noncomputable section

namespace Formalism.HadamardInequality.P

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem hadamard_inequality_holds : Formalism.HadamardInequality.Hadamard := by
  first | exact Bl.DetNormLeProdRows.goal1 .. | (apply Bl.DetNormLeProdRows.goal1 <;> assumption) | (intros; apply Bl.DetNormLeProdRows.goal1 <;> assumption)

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hadamard_maximum_holds : Formalism.HadamardInequality.HadamardMax := by
  unfold Formalism.HadamardInequality.HadamardMax
  intro ρ A M hM
  have hH := hadamard_inequality_holds
  unfold Formalism.HadamardInequality.Hadamard at hH
  refine (hH ρ A).trans ?_
  calc ∏ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∏ _i : Fin ρ, ((ρ : ℝ) * M ^ 2) := by
        refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun j _ => by positivity)
          fun i _ => ?_
        calc ∑ j, ‖A i j‖ ^ 2 ≤ ∑ _j : Fin ρ, M ^ 2 := by
              refine Finset.sum_le_sum fun j _ => ?_
              have hij := hM i j
              gcongr
          _ = (ρ : ℝ) * M ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ((ρ : ℝ) * M ^ 2) ^ ρ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Formalism.HadamardInequality.P
