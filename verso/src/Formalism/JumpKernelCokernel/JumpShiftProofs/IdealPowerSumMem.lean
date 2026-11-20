import Formalism.JumpKernelCokernel.Statement

namespace Formalism.KernelCokernelLengths.IdealPowerSumLemmas

/- English proof (translation)
Establish `hπ : π₀ ^ A ∈ Ideal.span {π₀ ^ A, ℓ ^ r}` using `Ideal.subset_span (Set.mem_insert _ _)`. Establish `hℓ : ℓ ^ r ∈ Ideal.span {π₀ ^ A, ℓ ^ r}` using `Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))`. Rewrite using `[add_pow]`. Use `Ideal.sum_mem _ fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i ≤ A + r - 1` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`.

Distinguish the cases in `hA : A ≤ i`. Establish `e : π₀ ^ i = π₀ ^ A * π₀ ^ (i - A)` using `by rw [← pow_add, Nat.add_sub_cancel' hA]`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hπ))`. Establish `hr : r ≤ A + r - 1 - i` using `by omega`.

Establish `e : ℓ ^ (A + r - 1 - i) = ℓ ^ r * ℓ ^ (A + r - 1 - i - r)`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hr]`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hℓ))`.
-/
theorem add_pow_mem_span_pow_pow (R : Type) [CommRing R] (π₀ ℓ : R) (A r : ℕ) :
    (π₀ + ℓ) ^ (A + r - 1) ∈ Ideal.span {π₀ ^ A, ℓ ^ r} := by
  have hπ : π₀ ^ A ∈ Ideal.span {π₀ ^ A, ℓ ^ r} := Ideal.subset_span (Set.mem_insert _ _)
  have hℓ : ℓ ^ r ∈ Ideal.span {π₀ ^ A, ℓ ^ r} :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rw [add_pow]
  refine Ideal.sum_mem _ fun i hi => ?_
  have hi' : i ≤ A + r - 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hA : A ≤ i
  · have e : π₀ ^ i = π₀ ^ A * π₀ ^ (i - A) := by rw [← pow_add, Nat.add_sub_cancel' hA]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hπ))
  · have hr : r ≤ A + r - 1 - i := by omega
    have e : ℓ ^ (A + r - 1 - i) = ℓ ^ r * ℓ ^ (A + r - 1 - i - r) := by
      rw [← pow_add, Nat.add_sub_cancel' hr]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hℓ))

end Formalism.KernelCokernelLengths.IdealPowerSumLemmas

/- English proof (translation)
Introduce `R _ π₀ ℓ A r`. Conclude with `Formalism.KernelCokernelLengths.IdealPowerSumLemmas.add_pow_mem_span_pow_pow R π₀ ℓ A r`.
-/
theorem Formalism.KernelCokernelLengths.ideal_power_sum_mem : Formalism.KernelCokernelLengths.QPow := by
  intro R _ π₀ ℓ A r
  exact Formalism.KernelCokernelLengths.IdealPowerSumLemmas.add_pow_mem_span_pow_pow R π₀ ℓ A r
