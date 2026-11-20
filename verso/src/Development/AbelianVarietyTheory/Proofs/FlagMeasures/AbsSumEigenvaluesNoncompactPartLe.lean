import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.EigenPartialSum

/- English proof (translation)
Unfold `Matrix.rank`. Rewrite using `[Matrix.mulVecLin_add]`. Use `le_trans (Submodule.finrank_mono ?_) (Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin))` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩`.
-/
theorem rank_add_le' {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  refine le_trans (Submodule.finrank_mono ?_)
    (Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range A.mulVecLin)
      (LinearMap.range B.mulVecLin))
  rintro _ ⟨x, rfl⟩
  exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

/- English proof (translation)
Use `set P : Matrix (Fin n) (Fin n) ℂ := diagonal fun a => if ε a = c then 1 else 0 with hP`. Establish `hY : Y = P * Y + Y * P`. Use extensionality with `a b`. Simplify using `only [hP, Matrix.add_apply, diagonal_mul, mul_diagonal]`. Distinguish the cases in `hab : ε a = ε b`.

Simplify using `[h0 a b hab]`. Distinguish the cases in `ha : ε a = c`. Establish `hb : ¬ ε b = c` using `fun hb => hab (ha.trans hb.symm)`. Simplify using `[ha, hb]`. Establish `hb : ε b = c` using `by revert hab ha`.

Apply the tactic sequence `cases ε a <;> cases ε b <;> cases c <;> simp`. Simplify using `[ha, hb]`. Establish `hr : P.rank = (univ.filter fun a => ε a = c).card`. Rewrite using `[hP, rank_diagonal, Fintype.card_subtype]`. Use `congr 1`.

Use extensionality with `a`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rank_le_two_mul {n : ℕ} (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ)
    (h0 : ∀ a b, ε a = ε b → Y a b = 0) (c : Bool) :
    Y.rank ≤ 2 * (univ.filter fun a => ε a = c).card := by
  classical
  set P : Matrix (Fin n) (Fin n) ℂ := diagonal fun a => if ε a = c then 1 else 0 with hP
  have hY : Y = P * Y + Y * P := by
    ext a b
    simp only [hP, Matrix.add_apply, diagonal_mul, mul_diagonal]
    by_cases hab : ε a = ε b
    · simp [h0 a b hab]
    · by_cases ha : ε a = c
      · have hb : ¬ ε b = c := fun hb => hab (ha.trans hb.symm)
        simp [ha, hb]
      · have hb : ε b = c := by
          revert hab ha
          cases ε a <;> cases ε b <;> cases c <;> simp
        simp [ha, hb]
  have hr : P.rank = (univ.filter fun a => ε a = c).card := by
    rw [hP, rank_diagonal, Fintype.card_subtype]
    congr 1
    ext a
    simp
  calc Y.rank = (P * Y + Y * P).rank := by rw [← hY]
    _ ≤ (P * Y).rank + (Y * P).rank := rank_add_le' _ _
    _ ≤ P.rank + P.rank := add_le_add (rank_mul_le_left _ _) (rank_mul_le_right _ _)
    _ = _ := by rw [hr]; ring

/- English proof (translation)
Establish `h1` using `congrFun (congrFun h.2 a) b`. Simplify using `only [Jm, mul_diagonal, diagonal_mul, Matrix.neg_apply, hab] at h1`. Apply the tactic sequence `cases hb : ε b <;> simp [hb] at h1`. Take the linear combination `(-1 / 2 : ℂ) * h1`. Take the linear combination `(1 / 2 : ℂ) * h1`.
-/
theorem apply_eq_zero_of_inP {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : inP ε Y) (a b : Fin n) (hab : ε a = ε b) : Y a b = 0 := by
  have h1 := congrFun (congrFun h.2 a) b
  simp only [Jm, mul_diagonal, diagonal_mul, Matrix.neg_apply, hab] at h1
  cases hb : ε b <;> simp [hb] at h1
  · linear_combination (-1 / 2 : ℂ) * h1
  · linear_combination (1 / 2 : ℂ) * h1

/- English proof (translation)
Establish `h1 : (Y * Y).trace = ((∑ j, hY.eigenvalues j ^ 2 : ℝ) : ℂ)` using `by conv_lhs => rw [hY.spectral_theorem, ← map_mul]`. Rewrite using `[Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, diagonal_mul_diagonal, trace_diagonal]`. Simplify using `[sq]`. Establish `h2 : (Y * Y).trace = ((hs Y : ℝ) : ℂ)`. Simplify using `only [trace, diag_apply, mul_apply, hs]`.

Use `push_cast`. Use `sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hY.apply j i, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Both sides reduce to the same expression.

Conclude with `h1.symm.trans h2` after adjusting the coercions.
-/
theorem sum_sq_eigenvalues {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) :
    ∑ j, hY.eigenvalues j ^ 2 = hs Y := by
  have h1 : (Y * Y).trace = ((∑ j, hY.eigenvalues j ^ 2 : ℝ) : ℂ) := by
    conv_lhs => rw [hY.spectral_theorem, ← map_mul]
    rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
      diagonal_mul_diagonal, trace_diagonal]
    simp [sq]
  have h2 : (Y * Y).trace = ((hs Y : ℝ) : ℂ) := by
    simp only [trace, diag_apply, mul_apply, hs]
    push_cast
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [← hY.apply j i, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  exact_mod_cast h1.symm.trans h2

/- English proof (translation)
Introduce `n ε Y hY hP J`. Use `set q : ℕ := min (univ.filter fun a => ε a = true).card (univ.filter fun a => ε a = false).card with hq`. Establish `hr : Y.rank ≤ 2 * q`. Establish `h1` using `rank_le_two_mul ε Y (apply_eq_zero_of_inP hP) true`. Establish `h2` using `rank_le_two_mul ε Y (apply_eq_zero_of_inP hP) false`.

Use linear arithmetic over natural numbers and integers. Use `set S := J.filter fun j => hY.eigenvalues j ≠ 0 with hS`. Establish `hc : S.card ≤ 2 * q`. Use `le_trans ?_ hr` and prove the remaining obligations. Rewrite using `[hY.rank_eq_card_non_zero_eigs, Fintype.card_subtype]`.

Conclude with `card_le_card (filter_subset_filter _ (subset_univ _))`. Establish `hc' : (S.card : ℝ) ≤ 2 * (q : ℝ)` using `by exact_mod_cast hc`. Establish `hsum : ∑ j ∈ J, hY.eigenvalues j = ∑ j ∈ S, hY.eigenvalues j` using `(sum_filter_ne_zero J).symm`. Establish `hsq : ∑ j ∈ S, hY.eigenvalues j ^ 2 ≤ hs Y`. Rewrite using `[← sum_sq_eigenvalues Y hY]`.

Conclude with `sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _`. Rewrite using `[hsum, ← Real.sqrt_mul (by positivity)]`. Use `Real.abs_le_sqrt (le_trans sq_sum_le_card_mul_sum_sq ?_)` and prove the remaining obligations. Conclude with `mul_le_mul hc' hsq (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)`.
-/
theorem abs_sum_eigenvalues_le : ∀ (n : ℕ) (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ)
    (hY : Y.IsHermitian), inP ε Y → ∀ J : Finset (Fin n), |∑ j ∈ J, hY.eigenvalues j| ≤
      Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card
        (univ.filter fun a => ε a = false).card : ℕ) : ℝ)) * Real.sqrt (hs Y) := by
  intro n ε Y hY hP J
  classical
  set q : ℕ := min (univ.filter fun a => ε a = true).card
    (univ.filter fun a => ε a = false).card with hq
  have hr : Y.rank ≤ 2 * q := by
    have h1 := rank_le_two_mul ε Y (apply_eq_zero_of_inP hP) true
    have h2 := rank_le_two_mul ε Y (apply_eq_zero_of_inP hP) false
    omega
  set S := J.filter fun j => hY.eigenvalues j ≠ 0 with hS
  have hc : S.card ≤ 2 * q := by
    refine le_trans ?_ hr
    rw [hY.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    exact card_le_card (filter_subset_filter _ (subset_univ _))
  have hc' : (S.card : ℝ) ≤ 2 * (q : ℝ) := by exact_mod_cast hc
  have hsum : ∑ j ∈ J, hY.eigenvalues j = ∑ j ∈ S, hY.eigenvalues j :=
    (sum_filter_ne_zero J).symm
  have hsq : ∑ j ∈ S, hY.eigenvalues j ^ 2 ≤ hs Y := by
    rw [← sum_sq_eigenvalues Y hY]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
  rw [hsum, ← Real.sqrt_mul (by positivity)]
  refine Real.abs_le_sqrt (le_trans sq_sum_le_card_mul_sum_sq ?_)
  exact mul_le_mul hc' hsq (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)

end GlobalTheory.EigenPartialSum
