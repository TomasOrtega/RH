import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsNormForm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Rewrite using `[coeff_sum, Finset.sum_eq_single i]`. Rewrite using `[mul_comm, coeff_C_mul, coeff_X]`. Simplify using the standard rewrite rules. Introduce `j _ hji`. Rewrite using `[mul_comm, coeff_C_mul, coeff_X, if_neg, mul_zero]`.

Introduce `h`. Conclude with `hji ((Finsupp.single_left_inj one_ne_zero).mp h)`. Simplify using the standard rewrite rules.
-/
theorem linearForm_coeff_single {F : Type} [Field F] {n : ℕ} (a : Fin n → F) (i : Fin n) :
    (∑ m, X m * C (a m) : MvPolynomial (Fin n) F).coeff (Finsupp.single i 1) = a i := by
  classical
  rw [coeff_sum, Finset.sum_eq_single i]
  · rw [mul_comm, coeff_C_mul, coeff_X]
    simp
  · intro j _ hji
    rw [mul_comm, coeff_C_mul, coeff_X, if_neg, mul_zero]
    intro h
    exact hji ((Finsupp.single_left_inj one_ne_zero).mp h)
  · simp

/- English proof (translation)
Introduce `F _ n a ha`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, a i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `ha (funext h)`.

Use `Irreducible.prime (irreducible_of_totalDegree_eq_one ?_ ?_)` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Use `(totalDegree_finsetSum _ _).trans (Finset.sup_le fun m _ => ?_)` and prove the remaining obligations. Use `(totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Rewrite using `[totalDegree_X, totalDegree_C]`.

Establish `hs : Finsupp.single i 1 ∈ (∑ m, X m * C (a m) : MvPolynomial (Fin n) F).support`. Rewrite using `[mem_support_iff, linearForm_coeff_single]`. Conclude with `hi`. Simplify using `using le_totalDegree hs`. Introduce `x hx`.

Establish `h` using `hx (Finsupp.single i 1)`. Rewrite `h` using `[linearForm_coeff_single]`. Use `isUnit_iff_ne_zero.mpr ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hi (zero_dvd_iff.mp h)`.
-/
theorem LinearFormPrime.proof : LinearFormPrime.Statement := by
  intro F _ n a ha
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  refine Irreducible.prime (irreducible_of_totalDegree_eq_one ?_ ?_)
  · apply le_antisymm
    · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m _ => ?_)
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X, totalDegree_C]
    · have hs : Finsupp.single i 1 ∈ (∑ m, X m * C (a m) : MvPolynomial (Fin n) F).support := by
        rw [mem_support_iff, linearForm_coeff_single]
        exact hi
      simpa using le_totalDegree hs
  · intro x hx
    have h := hx (Finsupp.single i 1)
    rw [linearForm_coeff_single] at h
    refine isUnit_iff_ne_zero.mpr ?_
    rintro rfl
    exact hi (zero_dvd_iff.mp h)

end

end GroundTheory.Heights₂.Heights
