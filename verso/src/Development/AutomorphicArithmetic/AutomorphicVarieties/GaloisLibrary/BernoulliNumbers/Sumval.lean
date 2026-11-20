import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

open Finset UpperTheory.V.Bern

/- English proof (translation)
Introduce `M hM T hT`. Establish `hN : M.natAbs ≠ 0` using `Int.natAbs_ne_zero.mpr hM`. Establish `hlog : Real.log |(M : ℝ)| = Real.log (M.natAbs : ℝ)`. Rewrite using `[Nat.cast_natAbs, Int.cast_abs]`. Rewrite using `[hlog, Real.log_nat_eq_sum_factorization, Finsupp.sum]`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite using `[Nat.factorization_def _ (hT l hl)]`. Both sides reduce to the same expression. Use `_ = ∑ l ∈ T.filter (· ∈ M.natAbs.factorization.support), (M.natAbs.factorization l : ℝ) * Real.log l := by`.

Use `(Finset.sum_filter_of_ne fun l _ h => ?_).symm` and prove the remaining obligations. Rewrite using `[Finsupp.mem_support_iff]`. Introduce `h0`. Apply `h` to reduce the goal to its premises. Simplify using `[h0]`.

Use `_ ≤ ∑ p ∈ M.natAbs.factorization.support, (M.natAbs.factorization p : ℝ) * Real.log p := by`. Use `Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => ?_` and prove the remaining obligations. Introduce `x hx`. Conclude with `(Finset.mem_filter.mp hx).2`. Conclude with `mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)`.
-/
theorem UpperTheory.V.Bern.b_sumval :
    ∀ (M : ℤ), M ≠ 0 → ∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → ∑ l ∈ T, (padicValInt l M : ℝ) * Real.log l ≤ Real.log |(M : ℝ)| := by
  intro M hM T hT
  have hN : M.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hM
  have hlog : Real.log |(M : ℝ)| = Real.log (M.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hlog, Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ l ∈ T, (padicValInt l M : ℝ) * Real.log l
      = ∑ l ∈ T, (M.natAbs.factorization l : ℝ) * Real.log l := by
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [Nat.factorization_def _ (hT l hl)]
        rfl
    _ = ∑ l ∈ T.filter (· ∈ M.natAbs.factorization.support),
          (M.natAbs.factorization l : ℝ) * Real.log l := by
        refine (Finset.sum_filter_of_ne fun l _ h => ?_).symm
        rw [Finsupp.mem_support_iff]
        intro h0
        apply h
        simp [h0]
    _ ≤ ∑ p ∈ M.natAbs.factorization.support,
          (M.natAbs.factorization p : ℝ) * Real.log p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => ?_
        · intro x hx
          exact (Finset.mem_filter.mp hx).2
        · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
