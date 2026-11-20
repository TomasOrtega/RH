import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Interface
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.IsIntegralOfRoot
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormLeOneOfIntegralInt

noncomputable section
open Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hsum` using `hm.as_sum`. Rewrite `h` using `[hsum]`. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_C] at h`.

Establish `hx1 : (1 : ℝ) ≤ ‖x‖` using `hlt.le`. Establish `hn0 : P.natDegree ≠ 0`. Introduce `h0`. Rewrite `h` using `[h0]`. Simplify using `at h`.

Establish `hbound : ‖∑ i ∈ Finset.range P.natDegree, (Int.castRingHom ℂ_[l]) (P.coeff i) * x ^ i‖ ≤ ‖x‖ ^ (P.natDegree - 1)`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[norm_mul, norm_pow]`.

Establish `hc : ‖(Int.castRingHom ℂ_[l]) (P.coeff i)‖ ≤ 1`. Rewrite using `[eq_intCast (Int.castRingHom ℂ_[l])]`. Conclude with `IsUltrametricDist.norm_intCast_le_one _ _`. Combine the equalities or inequalities in the displayed calculation. Establish `heq` using `eq_neg_of_add_eq_zero_left h`.

Establish `h1 : ‖x‖ ^ P.natDegree ≤ ‖x‖ ^ (P.natDegree - 1)`. Rewrite using `[← norm_pow, heq, norm_neg]`. Conclude with `hbound`. Establish `h2 : ‖x‖ ^ (P.natDegree - 1) < ‖x‖ ^ P.natDegree` using `pow_lt_pow_right₀ hlt (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_le_one_of_root {l : ℕ} [Fact l.Prime] {x : ℂ_[l]} (P : Polynomial ℤ) (hm : P.Monic)
    (h : P.eval₂ (Int.castRingHom ℂ_[l]) x = 0) : ‖x‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  have hsum := hm.as_sum
  rw [hsum] at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at h
  have hx1 : (1 : ℝ) ≤ ‖x‖ := hlt.le
  have hn0 : P.natDegree ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  have hbound : ‖∑ i ∈ Finset.range P.natDegree, (Int.castRingHom ℂ_[l]) (P.coeff i) * x ^ i‖ ≤
      ‖x‖ ^ (P.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow]
    have hc : ‖(Int.castRingHom ℂ_[l]) (P.coeff i)‖ ≤ 1 := by
      rw [eq_intCast (Int.castRingHom ℂ_[l])]
      exact IsUltrametricDist.norm_intCast_le_one _ _
    calc ‖(Int.castRingHom ℂ_[l]) (P.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (P.natDegree - 1) :=
          mul_le_mul hc (pow_le_pow_right₀ hx1 (by omega)) (by positivity) zero_le_one
      _ = ‖x‖ ^ (P.natDegree - 1) := one_mul _
  have heq := eq_neg_of_add_eq_zero_left h
  have h1 : ‖x‖ ^ P.natDegree ≤ ‖x‖ ^ (P.natDegree - 1) := by
    rw [← norm_pow, heq, norm_neg]
    exact hbound
  have h2 : ‖x‖ ^ (P.natDegree - 1) < ‖x‖ ^ P.natDegree := pow_lt_pow_right₀ hlt (by omega)
  linarith

/- English proof (translation)
Introduce `d L hsf hd hL l _ ι`. Take `⟨P, hm, hP⟩` from `cm1 d L hsf hd hL`. Use `norm_le_one_of_root P hm ?_` and prove the remaining obligations. Establish `h` using `congrArg (ι : ℂ →+* ℂ_[l]) hP`. Rewrite `h` using `[Polynomial.hom_eval₂, map_zero]`.

Rewrite using `[← h]`. Use `congr 1`. Conclude with `Subsingleton.elim _ _`.
-/
theorem jInt : JInt := by
  intro d L hsf hd hL l _ ι
  obtain ⟨P, hm, hP⟩ := cm1 d L hsf hd hL
  refine norm_le_one_of_root P hm ?_
  have h := congrArg (ι : ℂ →+* ℂ_[l]) hP
  rw [Polynomial.hom_eval₂, map_zero] at h
  rw [← h]
  congr 1
  exact Subsingleton.elim _ _

end ReciprocityTheory.ChartRestriction.L1
