import Formalism.GradedWeylDivisibility.StatementD

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `m hm`. Simplify using `only [ssIdx, Set.mem_setOf_eq] at hm`. Rewrite using `[Set.mem_Iic]`. Introduce `v`. Take `⟨a, t⟩` from `v`.

Use `show m (a, t) ≤ ν t`. Rewrite using `[← hm.2 t]`. Conclude with `Finset.single_le_sum (f := fun a' => m (a', t)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)`.
-/
theorem ldbasis_ssIdx_subset_Iic (k n : ℕ) (ν : Fin n → ℕ) :
    ssIdx k n ν ⊆ Set.Iic (Finsupp.equivFunOnFinite.symm (fun v : Fin k × Fin n => ν v.2)) := by
  intro m hm
  simp only [ssIdx, Set.mem_setOf_eq] at hm
  rw [Set.mem_Iic]
  intro v
  obtain ⟨a, t⟩ := v
  show m (a, t) ≤ ν t
  rw [← hm.2 t]
  exact Finset.single_le_sum (f := fun a' => m (a', t)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

/- English proof (translation)
Introduce `k n ν`. Conclude with `(Set.finite_Iic _).subset (ldbasis_ssIdx_subset_Iic k n ν)`.
-/
theorem semistandard_index_finite : SSIdxFinite := by
  intro k n ν
  exact (Set.finite_Iic _).subset (ldbasis_ssIdx_subset_Iic k n ν)

end Formalism.GradedWeylDivisibility
