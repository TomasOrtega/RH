import Formalism.GradedWeylDivisibility.StatementA

namespace Formalism.GradedWeylDivisibility

open MvPolynomial

/- English proof (translation)
Introduce `r n ν hn k`. Set `g : ℕ → ℕ` to `fun i => if i < k then (if h : i < n then ν ⟨i, h⟩ else 0) else 0`. Establish `hL : ∑ a : Fin r with a.val < k, rowNu (r` using `r) ν a = ∑ i ∈ Finset.range r, g i := by`. Rewrite using `[Finset.sum_filter, ← Fin.sum_univ_eq_sum_range g r]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Simplify using `only [g, rowNu]`. Establish `hR : ∑ t : Fin n with t.val < k, ν t = ∑ i ∈ Finset.range n, g i`. Rewrite using `[Finset.sum_filter, ← Fin.sum_univ_eq_sum_range g n]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Simplify using `only [g, dif_pos t.isLt]`.

Rewrite using `[hL, hR]`. Use `(Finset.sum_subset (fun i hi => ?_) (fun i hi hni => ?_)).symm` and prove the remaining obligations. Simplify using `only [Finset.mem_range] at hi ⊢`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Finset.mem_range] at hi hni`.

Simplify using `only [g, dif_neg hni, ite_self]`.
-/
theorem rowPartSum : RowNuSum := by
  classical
  intro r n ν hn k
  let g : ℕ → ℕ := fun i => if i < k then (if h : i < n then ν ⟨i, h⟩ else 0) else 0
  have hL : ∑ a : Fin r with a.val < k, rowNu (r := r) ν a = ∑ i ∈ Finset.range r, g i := by
    rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range g r]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [g, rowNu]
  have hR : ∑ t : Fin n with t.val < k, ν t = ∑ i ∈ Finset.range n, g i := by
    rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range g n]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [g, dif_pos t.isLt]
  rw [hL, hR]
  refine (Finset.sum_subset (fun i hi => ?_) (fun i hi hni => ?_)).symm
  · simp only [Finset.mem_range] at hi ⊢; omega
  · simp only [Finset.mem_range] at hi hni
    simp only [g, dif_neg hni, ite_self]

end Formalism.GradedWeylDivisibility
