import Formalism.EllipticTorsion.Statement
import Formalism.EllipticTorsion.EllipticTorsionProofs.LegendreInvariant

namespace Formalism.ELL

namespace LegendreModelEllipticTorsion

open Polynomial

noncomputable def legPoly {K : Type*} [Field K] (j : K) : K[X] :=
  C 256 * (X ^ 2 - X + 1) ^ 3 - C j * (X * (X - 1)) ^ 2

/- English proof (translation)
Unfold `legPoly`. Use `compute_degree!`.
-/
theorem legPoly_natDegree {K : Type*} [Field K] (h : (256 : K) ≠ 0) (j : K) :
    (legPoly j).natDegree = 6 := by
  unfold legPoly
  compute_degree!

/- English proof (translation)
Use `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (1 : K)) (y := t) (by rw [norm_one]; exact fun h => ht h.symm)` as an intermediate fact. Simplify using `using this`.
-/
theorem norm_one_add {K : Type*} [NormedField K] [IsUltrametricDist K] {t : K} (ht : ‖t‖ ≠ 1) :
    ‖1 + t‖ = max 1 ‖t‖ := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (1 : K)) (y := t)
    (by rw [norm_one]; exact fun h => ht h.symm)
  simpa using this

end LegendreModelEllipticTorsion

open LegendreModelEllipticTorsion Polynomial in
/- English proof (translation)
Introduce `K _ _ _ h2 j hj`. Establish `h16 : ‖(16 : K)‖ = 1`. Establish `: (16 : K) = 2 ^ 4` using `by norm_num`. Rewrite using `[this, norm_pow, h2, one_pow]`. Establish `h256 : ‖(256 : K)‖ = 1`.

Establish `: (256 : K) = 2 ^ 8` using `by norm_num`. Rewrite using `[this, norm_pow, h2, one_pow]`. Establish `h256ne : (256 : K) ≠ 0`. Introduce `h`. Rewrite `h256` using `[h, norm_zero]`.

Conclude with `zero_ne_one h256`. Establish `hdeg : (legPoly j).degree ≠ 0`. Rewrite using `[degree_eq_natDegree, legPoly_natDegree h256ne]`. Evaluate the decidable proposition. Introduce `h0`.

Use `legPoly_natDegree h256ne j` as an intermediate fact. Rewrite `this` using `[h0, natDegree_zero]`. Conclude with `absurd this (by decide)`. Take `⟨l, hl⟩` from `IsAlgClosed.exists_root _ hdeg`. Establish `hroot : (256 : K) * (l ^ 2 - l + 1) ^ 3 = j * (l * (l - 1)) ^ 2`.

Use `hl.eq_zero` as an intermediate fact. Simplify using `only [legPoly, eval_sub, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one] at this`. Conclude with `sub_eq_zero.mp this`. Use `set t := l * (l - 1) with ht`. Establish `hu : l ^ 2 - l + 1 = 1 + t` using `by rw [ht]; ring`.

Rewrite `hroot` using `[hu]`. Establish `hnorm` using `congrArg norm hroot`. Simplify using `only [norm_mul, norm_pow, h256, one_mul] at hnorm`. Establish `htn : ‖t‖ = 1`. Assume the negation of the conclusion as `hne`.

Establish `e` using `norm_one_add hne`. Break down `lt_or_gt_of_ne hne with hlt | hgt` into its components or cases. Rewrite `hnorm` using `[e, max_eq_left hlt.le, one_pow]`. Establish `: ‖j‖ * ‖t‖ ^ 2 < 1`. Combine the equalities or inequalities in the displayed calculation.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hnorm` using `[e, max_eq_right hgt.le]`. Establish `hpos : 0 < ‖t‖ ^ 2` using `by positivity`. Establish `: ‖t‖ ^ 3 ≤ ‖t‖ ^ 2`. Rewrite using `[hnorm]; calc ‖j‖ * ‖t‖ ^ 2 ≤ 1 * ‖t‖ ^ 2 := by gcongr _ = ‖t‖ ^ 2 := one_mul _`.

Establish `: ‖t‖ ^ 2 * ‖t‖ ≤ ‖t‖ ^ 2 * 1` using `by nlinarith`. Use `le_of_mul_le_mul_left this hpos` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hprod : ‖l‖ * ‖l - 1‖ = 1` using `by rw [← norm_mul, ← ht, htn]`. Establish `hle1 : ‖l - 1‖ ≤ max ‖l‖ 1`.

Use `IsUltrametricDist.norm_add_le_max l (-1 : K)` as an intermediate fact. Simplify `this` using `[← sub_eq_add_neg]`. Establish `hle2 : ‖l‖ ≤ max ‖l - 1‖ 1`. Use `IsUltrametricDist.norm_add_le_max (l - 1) (1 : K)` as an intermediate fact. Simplify using `using this`.

Establish `hl1 : ‖l‖ = 1`. Break down `lt_trichotomy ‖l‖ 1 with h | h | h` into its components or cases. It suffices to derive a contradiction. Rewrite `hle1` using `[max_eq_right h.le]`. Establish `: ‖l‖ * ‖l - 1‖ < 1`.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h`. It suffices to derive a contradiction. Establish `hpos : 0 < ‖l‖` using `by linarith`.

Establish `hlt : ‖l - 1‖ < 1`. Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_lt]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite `hle2` using `[max_eq_right hlt.le]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hl2 : ‖l - 1‖ = 1` using `by rw [hl1, one_mul] at hprod; exact hprod`. Take `⟨hΔ, hc4⟩` from `legendre_invariant K l`. Use `⟨l, hl1, hl2, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hΔ, hc4]`.

Establish `: (l ^ 2 - l + 1) = 1 + t` using `hu`. Rewrite using `[this]`. Establish `e2 : (16 : K) * l ^ 2 * (l - 1) ^ 2 = 16 * t ^ 2` using `by rw [ht]; ring`. Rewrite using `[e2]`. Take the linear combination `16 * hroot`.

Rewrite using `[hΔ, norm_mul, norm_mul, h16, norm_pow, norm_pow, hl1, hl2]`. Evaluate the numerical expressions.
-/
theorem legendre_model : ModelLegendre := by
  intro K _ _ _ h2 j hj
  have h16 : ‖(16 : K)‖ = 1 := by
    have : (16 : K) = 2 ^ 4 := by norm_num
    rw [this, norm_pow, h2, one_pow]
  have h256 : ‖(256 : K)‖ = 1 := by
    have : (256 : K) = 2 ^ 8 := by norm_num
    rw [this, norm_pow, h2, one_pow]
  have h256ne : (256 : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at h256; exact zero_ne_one h256
  have hdeg : (legPoly j).degree ≠ 0 := by
    rw [degree_eq_natDegree, legPoly_natDegree h256ne]
    · decide
    · intro h0
      have := legPoly_natDegree h256ne j
      rw [h0, natDegree_zero] at this
      exact absurd this (by decide)
  obtain ⟨l, hl⟩ := IsAlgClosed.exists_root _ hdeg
  have hroot : (256 : K) * (l ^ 2 - l + 1) ^ 3 = j * (l * (l - 1)) ^ 2 := by
    have := hl.eq_zero
    simp only [legPoly, eval_sub, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one] at this
    exact sub_eq_zero.mp this
  set t := l * (l - 1) with ht
  have hu : l ^ 2 - l + 1 = 1 + t := by rw [ht]; ring
  rw [hu] at hroot
  have hnorm := congrArg norm hroot
  simp only [norm_mul, norm_pow, h256, one_mul] at hnorm

  have htn : ‖t‖ = 1 := by
    by_contra hne
    have e := norm_one_add hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [e, max_eq_left hlt.le, one_pow] at hnorm
      have : ‖j‖ * ‖t‖ ^ 2 < 1 := by
        calc ‖j‖ * ‖t‖ ^ 2 ≤ 1 * ‖t‖ ^ 2 := by gcongr
          _ < 1 := by rw [one_mul]; exact pow_lt_one₀ (norm_nonneg _) hlt (by norm_num)
      linarith
    · rw [e, max_eq_right hgt.le] at hnorm
      have hpos : 0 < ‖t‖ ^ 2 := by positivity
      have : ‖t‖ ^ 3 ≤ ‖t‖ ^ 2 := by
        rw [hnorm]; calc ‖j‖ * ‖t‖ ^ 2 ≤ 1 * ‖t‖ ^ 2 := by gcongr
          _ = ‖t‖ ^ 2 := one_mul _
      have : ‖t‖ ^ 2 * ‖t‖ ≤ ‖t‖ ^ 2 * 1 := by nlinarith
      have := le_of_mul_le_mul_left this hpos
      linarith
  have hprod : ‖l‖ * ‖l - 1‖ = 1 := by rw [← norm_mul, ← ht, htn]
  have hle1 : ‖l - 1‖ ≤ max ‖l‖ 1 := by
    have := IsUltrametricDist.norm_add_le_max l (-1 : K)
    simpa [← sub_eq_add_neg] using this
  have hle2 : ‖l‖ ≤ max ‖l - 1‖ 1 := by
    have := IsUltrametricDist.norm_add_le_max (l - 1) (1 : K)
    simpa using this
  have hl1 : ‖l‖ = 1 := by
    rcases lt_trichotomy ‖l‖ 1 with h | h | h
    · exfalso
      rw [max_eq_right h.le] at hle1
      have : ‖l‖ * ‖l - 1‖ < 1 := by
        calc ‖l‖ * ‖l - 1‖ ≤ ‖l‖ * 1 := by gcongr
          _ < 1 := by rw [mul_one]; exact h
      linarith
    · exact h
    · exfalso
      have hpos : 0 < ‖l‖ := by linarith
      have hlt : ‖l - 1‖ < 1 := by
        by_contra hc
        rw [not_lt] at hc
        nlinarith
      rw [max_eq_right hlt.le] at hle2
      linarith
  have hl2 : ‖l - 1‖ = 1 := by rw [hl1, one_mul] at hprod; exact hprod
  obtain ⟨hΔ, hc4⟩ := legendre_invariant K l
  refine ⟨l, hl1, hl2, ?_, ?_⟩
  · rw [hΔ, hc4]
    have : (l ^ 2 - l + 1) = 1 + t := hu
    rw [this]
    have e2 : (16 : K) * l ^ 2 * (l - 1) ^ 2 = 16 * t ^ 2 := by rw [ht]; ring
    rw [e2]
    linear_combination 16 * hroot
  · rw [hΔ, norm_mul, norm_mul, h16, norm_pow, norm_pow, hl1, hl2]
    norm_num

end Formalism.ELL
