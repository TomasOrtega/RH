import Mathlib

/- English proof (translation)
Introduce `m n x`. Establish `hS : 0 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ)` using `Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => by positivity`. Establish `hle : ‖x‖ ≤ Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ))`. Use `(pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_` and prove the remaining obligations.

Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.Reformulated.B.DYka1.main :
    ∀ {m n : ℕ} (x : Fin m → Fin n → ℂ), ‖x‖ ^ (2 : ℕ) ≤ ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) := by
  intro m n x
  have hS : 0 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => by positivity
  have hle : ‖x‖ ≤ Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    apply Real.le_sqrt_of_sq_le
    calc ‖x a i‖ ^ (2 : ℕ) ≤ ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
          Finset.single_le_sum (f := fun j : Fin n => ‖x a j‖ ^ (2 : ℕ))
            (fun j _ => by positivity) (Finset.mem_univ i)
      _ ≤ ∑ b : Fin m, ∑ j : Fin n, ‖x b j‖ ^ (2 : ℕ) :=
          Finset.single_le_sum (f := fun b : Fin m => ∑ j : Fin n, ‖x b j‖ ^ (2 : ℕ))
            (fun b _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ a)
  calc ‖x‖ ^ (2 : ℕ) ≤ (Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ))) ^ (2 : ℕ) := by
        gcongr
    _ = ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) := Real.sq_sqrt hS
