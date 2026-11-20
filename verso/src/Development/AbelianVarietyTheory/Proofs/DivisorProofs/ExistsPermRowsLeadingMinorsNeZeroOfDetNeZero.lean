import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory

/- English proof (translation)
Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `A _`. Use `⟨1, fun k hk => ?_⟩` and prove the remaining obligations.

Take `rfl : k = 0` from `by omega`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `A hA`. Establish `h1 : ∃ i : Fin (n + 1), (A.submatrix i.succAbove (Fin.last n).succAbove).det ≠ 0`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hA` to reduce the goal to its premises. Rewrite using `[Matrix.det_succ_column A (Fin.last n)]`. Simplify using `only [h, mul_zero, Finset.sum_const_zero]`.

Take `⟨i, hi⟩` from `h1`. Take `⟨w', hw'⟩` from `ih _ hi`. Set `w : Equiv.Perm (Fin (n + 1))` to `(finSuccEquiv' (Fin.last n)).trans ((Equiv.optionCongr w').trans (finSuccEquiv' i).symm)`. Establish `hw : ∀ j : Fin n, w ((Fin.last n).succAbove j) = i.succAbove (w' j)`. Introduce `j`.

Simplify using `only [w, Equiv.trans_apply, finSuccEquiv'_succAbove, Equiv.optionCongr_apply, Option.map_some, finSuccEquiv'_symm_some]`. Use `⟨w, fun k hk => ?_⟩` and prove the remaining obligations. Break down `Nat.lt_or_ge n k with hlt | hle` into its components or cases. Take `rfl : k = n + 1` from `by omega`. Establish `: (Fin.castLE hk : Fin (n + 1) → Fin (n + 1)) = id`.

Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Rewrite using `[this, Matrix.submatrix_id_id, Matrix.det_permute]`. Use `mul_ne_zero ?_ hA` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h | h <;> simp [h]`.

Establish `hc : ∀ x : Fin k, (Fin.castLE hk x : Fin (n + 1)) = (Fin.last n).succAbove (Fin.castLE hle x)`. Introduce `x`. Rewrite using `[Fin.succAbove_last]`. Both sides reduce to the same expression. Use `hw' k hle using 2` and compare the differences between its conclusion and the goal.

Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, id, hc, hw]`.
-/
theorem exists_perm_rows_leading_minors_ne_zero_of_det_ne_zero (K : Type) [Field K] :
    ∀ (N : ℕ) (A : Matrix (Fin N) (Fin N) K), A.det ≠ 0 →
      ∃ w : Equiv.Perm (Fin N), ∀ (k : ℕ) (hk : k ≤ N),
        ((A.submatrix w id).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
  intro N
  induction N with
  | zero =>
    intro A _
    refine ⟨1, fun k hk => ?_⟩
    obtain rfl : k = 0 := by omega
    simp
  | succ n ih =>
    intro A hA
    have h1 : ∃ i : Fin (n + 1),
        (A.submatrix i.succAbove (Fin.last n).succAbove).det ≠ 0 := by
      by_contra h
      push_neg at h
      apply hA
      rw [Matrix.det_succ_column A (Fin.last n)]
      simp only [h, mul_zero, Finset.sum_const_zero]
    obtain ⟨i, hi⟩ := h1
    obtain ⟨w', hw'⟩ := ih _ hi
    let w : Equiv.Perm (Fin (n + 1)) :=
      (finSuccEquiv' (Fin.last n)).trans ((Equiv.optionCongr w').trans (finSuccEquiv' i).symm)
    have hw : ∀ j : Fin n, w ((Fin.last n).succAbove j) = i.succAbove (w' j) := by
      intro j
      simp only [w, Equiv.trans_apply, finSuccEquiv'_succAbove, Equiv.optionCongr_apply,
        Option.map_some, finSuccEquiv'_symm_some]
    refine ⟨w, fun k hk => ?_⟩
    rcases Nat.lt_or_ge n k with hlt | hle
    · obtain rfl : k = n + 1 := by omega
      have : (Fin.castLE hk : Fin (n + 1) → Fin (n + 1)) = id := by
        funext x; simp
      rw [this, Matrix.submatrix_id_id, Matrix.det_permute]
      refine mul_ne_zero ?_ hA
      rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h | h <;> simp [h]
    · have hc : ∀ x : Fin k, (Fin.castLE hk x : Fin (n + 1))
          = (Fin.last n).succAbove (Fin.castLE hle x) := by
        intro x
        rw [Fin.succAbove_last]
        rfl
      convert hw' k hle using 2
      ext a b
      simp only [Matrix.submatrix_apply, id, hc, hw]

/- English proof (translation)
Introduce `K _ N g`. Conclude with `exists_perm_rows_leading_minors_ne_zero_of_det_ne_zero K N g.1 (Matrix.GeneralLinearGroup.det_ne_zero g)`.
-/
theorem GL_exists_perm_rows_leading_minors_ne_zero :
    ∀ (K : Type) [Field K] (N : ℕ) (g : GL (Fin N) K), ∃ w : Equiv.Perm (Fin N),
      ∀ (k : ℕ) (hk : k ≤ N),
        ((g.1.submatrix w id).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
  intro K _ N g
  exact exists_perm_rows_leading_minors_ne_zero_of_det_ne_zero K N g.1
    (Matrix.GeneralLinearGroup.det_ne_zero g)

end GlobalTheory
