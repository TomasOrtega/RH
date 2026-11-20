import Mathlib
import Formalism.GelfandTransference.Statement
import Lemmata.DetNormLeProdRows.DetNormLeProdRows

open Matrix Finset
open scoped ComplexOrder

noncomputable section

namespace Formalism.HadamardInequality.P

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.DetNormLeProdRows.goal1 .. | (apply Bl.DetNormLeProdRows.goal1 <;> assumption) | (intros; apply Bl.DetNormLeProdRows.goal1 <;> assumption)`.
-/
theorem hadamard_inequality_holds : Formalism.HadamardInequality.Hadamard := by
  first | exact Bl.DetNormLeProdRows.goal1 .. | (apply Bl.DetNormLeProdRows.goal1 <;> assumption) | (intros; apply Bl.DetNormLeProdRows.goal1 <;> assumption)

/- English proof (translation)
Unfold `Formalism.HadamardInequality.HadamardMax`. Introduce `ρ A M hM`. Establish `hH` using `hadamard_inequality_holds`. Unfold `Formalism.HadamardInequality.Hadamard at hH`. Use `(hH ρ A).trans ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun j _ => by positivity) fun i _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Establish `hij` using `hM i j`.

Use `gcongr`. Use `_ = (ρ : ℝ) * M ^ 2 := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Use `_ = ((ρ : ℝ) * M ^ 2) ^ ρ := by`. Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
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
