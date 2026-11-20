import Mathlib
open MvPolynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `D T₀ q hq`. Use `⟨∑ d ∈ Finset.range (q + 1), X 0 ^ (q - d) * rename Fin.succ (homogeneousComponent d T₀), ?_, ?_⟩` and prove the remaining obligations. Apply `IsHomogeneous.sum` to reduce the goal to its premises. Introduce `d hd`. Establish `hdq : d ≤ q` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)`.

Establish `h` using `(isHomogeneous_X_pow (R := ℤ) (0 : Fin (D + 1)) (q - d)).mul ((homogeneousComponent_isHomogeneous d T₀).rename_isHomogeneous (f := Fin.succ))`. Rewrite `h` using `[Nat.sub_add_cancel hdq]`. Then use the resulting hypothesis. Introduce `R _ a ha`. Establish `hsum : ∑ d ∈ Finset.range (q + 1), homogeneousComponent d T₀ = T₀` using `by conv_rhs => rw [← sum_homogeneousComponent T₀]`. Use `symm`.

Use `Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hq)) ?_` and prove the remaining obligations. Introduce `x _ hx`. Apply `homogeneousComponent_eq_zero` to reduce the goal to its premises. Simplify using `only [Finset.mem_range] at hx`. Use linear arithmetic over natural numbers and integers.

Use `conv_rhs => rw [← hsum]`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl ?_` and prove the remaining obligations. Introduce `d _`. Simplify using `only [map_mul, map_pow, aeval_X, ha, one_pow, one_mul, aeval_rename]`.

Both sides reduce to the same expression.
-/
theorem exists_isHomogeneous_dehomogenize : ∀ {D : ℕ} (T₀ : MvPolynomial (Fin D) ℤ) (q : ℕ),
    T₀.totalDegree ≤ q → ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous q ∧
      ∀ (R : Type) [CommRing R] (a : Fin (D + 1) → R), a 0 = 1 →
        aeval a T = aeval (fun j => a j.succ) T₀ := by
  intro D T₀ q hq
  refine ⟨∑ d ∈ Finset.range (q + 1),
    X 0 ^ (q - d) * rename Fin.succ (homogeneousComponent d T₀), ?_, ?_⟩
  · apply IsHomogeneous.sum
    intro d hd
    have hdq : d ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    have h := (isHomogeneous_X_pow (R := ℤ) (0 : Fin (D + 1)) (q - d)).mul
      ((homogeneousComponent_isHomogeneous d T₀).rename_isHomogeneous (f := Fin.succ))
    rwa [Nat.sub_add_cancel hdq] at h
  · intro R _ a ha
    have hsum : ∑ d ∈ Finset.range (q + 1), homogeneousComponent d T₀ = T₀ := by
      conv_rhs => rw [← sum_homogeneousComponent T₀]
      symm
      refine Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hq)) ?_
      intro x _ hx
      apply homogeneousComponent_eq_zero
      simp only [Finset.mem_range] at hx
      omega
    conv_rhs => rw [← hsum]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl ?_
    intro d _
    simp only [map_mul, map_pow, aeval_X, ha, one_pow, one_mul, aeval_rename]
    rfl

end GlobalTheory
