import Mathlib

namespace EqOneOfPowersNearOne

/- English proof (translation)
Use `set S : R := ∑ k ∈ Finset.range N, a ^ k with hS`. Establish `hgeom : S * (a - 1) = a ^ N - 1` using `geom_sum_mul a N`. Establish `hdiff : (N : R) - S = ∑ k ∈ Finset.range N, ((1 : R) - a ^ k)`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]`. Establish `hbound : ‖(N : R) - S‖ ≤ N / 2`.

Rewrite using `[hdiff]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `k _`. Rewrite using `[norm_sub_rev]`.

Conclude with `(h k).le`. Use `_ = N / 2 := by simp; ring`. Establish `hnorm : ‖(N : R) * (a - 1)‖ = (N : ℝ) * ‖a - 1‖`. Establish `: (N : R) * (a - 1) = (N : ℂ) • (a - 1)`. Rewrite using `[Algebra.smul_def]`.

Simplify using the standard rewrite rules. Rewrite using `[this, norm_smul]`. Simplify using the standard rewrite rules. Establish `hsplit : (N : R) * (a - 1) = ((N : R) - S) * (a - 1) + S * (a - 1)`. Rewrite using `[sub_mul]`.

Normalize the expressions using the abelian group laws. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hgeom]`. Use `gcongr`. Conclude with `norm_mul_le _ _`.

Use `_ < ‖a - 1‖ * (N / 2) + 1 / 2 := by`. Use `h N` as an intermediate fact. Use polynomial arithmetic with `[norm_nonneg (a - 1)]`.
-/
private lemma key {R : Type} [NormedRing R] [NormedAlgebra ℂ R] {a : R}
    (h : ∀ (p : ℕ), ‖a ^ p - (1 : R)‖ < (1 / 2 : ℝ)) (N : ℕ) :
    (N : ℝ) * ‖a - 1‖ < ‖a - 1‖ * (N / 2) + 1 / 2 := by
  set S : R := ∑ k ∈ Finset.range N, a ^ k with hS
  have hgeom : S * (a - 1) = a ^ N - 1 := geom_sum_mul a N
  have hdiff : (N : R) - S = ∑ k ∈ Finset.range N, ((1 : R) - a ^ k) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hbound : ‖(N : R) - S‖ ≤ N / 2 := by
    rw [hdiff]
    calc ‖∑ k ∈ Finset.range N, ((1 : R) - a ^ k)‖
        ≤ ∑ k ∈ Finset.range N, ‖(1 : R) - a ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range N, (1 / 2 : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          rw [norm_sub_rev]; exact (h k).le
      _ = N / 2 := by simp; ring
  have hnorm : ‖(N : R) * (a - 1)‖ = (N : ℝ) * ‖a - 1‖ := by
    have : (N : R) * (a - 1) = (N : ℂ) • (a - 1) := by
      rw [Algebra.smul_def]; simp
    rw [this, norm_smul]; simp
  have hsplit : (N : R) * (a - 1) = ((N : R) - S) * (a - 1) + S * (a - 1) := by
    rw [sub_mul]; abel
  calc (N : ℝ) * ‖a - 1‖ = ‖(N : R) * (a - 1)‖ := hnorm.symm
    _ ≤ ‖((N : R) - S) * (a - 1)‖ + ‖S * (a - 1)‖ := by rw [hsplit]; exact norm_add_le _ _
    _ ≤ ‖(N : R) - S‖ * ‖a - 1‖ + ‖a ^ N - 1‖ := by
        rw [hgeom]; gcongr; exact norm_mul_le _ _
    _ < ‖a - 1‖ * (N / 2) + 1 / 2 := by
        have := h N
        nlinarith [norm_nonneg (a - 1)]

end EqOneOfPowersNearOne

/- English proof (translation)
Introduce `R _ _ a h`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖a - 1‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr hne)`. Take `⟨N, hN⟩` from `exists_nat_gt (1 / ‖a - 1‖)`. Establish `hk` using `EqOneOfPowersNearOne.key h N`.

Establish `h1 : 1 < (N : ℝ) * ‖a - 1‖`. Rewrite `hN` using `[div_lt_iff₀ hpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem UpperTheory.Reformulated.B.Yhd7.main :
    ∀ {R : Type} [inst : NormedRing R] [NormedAlgebra ℂ R] {a : R},
      (∀ (p : ℕ), ‖a ^ p - (1 : R)‖ < (1 / 2 : ℝ)) → a = (1 : R) := by
  intro R _ _ a h
  by_contra hne
  have hpos : 0 < ‖a - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖a - 1‖)
  have hk := EqOneOfPowersNearOne.key h N
  have h1 : 1 < (N : ℝ) * ‖a - 1‖ := by
    rw [div_lt_iff₀ hpos] at hN; linarith
  nlinarith
