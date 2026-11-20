import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassTop

/- English proof (translation)
Establish `key : ∀ k, homogeneousComponent (k + b) (P * Q) = homogeneousComponent k P * Q`. Introduce `k`. Use `conv_lhs => rw [← sum_homogeneousComponent P]`. Rewrite using `[Finset.sum_mul, map_sum]`. Establish `hterm : ∀ i, homogeneousComponent (k + b) (homogeneousComponent i P * Q) = if i = k then homogeneousComponent i P * Q else 0`.

Introduce `i`. Establish `hm : homogeneousComponent i P * Q ∈ homogeneousSubmodule σ ℝ (i + b)` using `(homogeneousComponent_isHomogeneous i P).mul hQh`. Rewrite using `[homogeneousComponent_of_mem hm]`. Distinguish the cases in `h : i = k`. Simplify using `[h]`.

Establish `: k + b ≠ i + b` using `by omega`. Rewrite using `[if_neg this, if_neg h]`. Repeatedly rewrite using `[hterm]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with h`.

Use `subst_vars`. Both sides reduce to the same expression. Simplify using `only [Finset.mem_range, not_lt] at h`. Rewrite using `[homogeneousComponent_eq_zero k P (by omega), zero_mul]`. Establish `hzero : ∀ k, k ≠ a → homogeneousComponent k P = 0`.

Introduce `k hk`. Establish `h1 : homogeneousComponent (k + b) (P * Q) = 0`. Establish `: k + b ≠ a + b` using `by omega`. Establish `e` using `homogeneousComponent_of_mem (m := k + b) (hPQ : P * Q ∈ homogeneousSubmodule σ ℝ (a + b))`. Rewrite using `[e, if_neg this]`.

Rewrite `h1` using `[key]`. Conclude with `(mul_eq_zero.mp h1).resolve_right hQ`. Rewrite using `[← sum_homogeneousComponent P]`. Apply `IsHomogeneous.sum` to reduce the goal to its premises. Introduce `k _`.

Distinguish the cases in `hk : k = a`. Substitute `hk` using the available equality. Conclude with `homogeneousComponent_isHomogeneous k P`. Rewrite using `[hzero k hk]`. Conclude with `isHomogeneous_zero _ _ _`.
-/
theorem isHomogeneous_of_mul_isHomogeneous_right {σ : Type} (P Q : MvPolynomial σ ℝ) (a b : ℕ)
    (hQ : Q ≠ 0) (hQh : Q.IsHomogeneous b) (hPQ : (P * Q).IsHomogeneous (a + b)) :
    P.IsHomogeneous a := by
  have key : ∀ k, homogeneousComponent (k + b) (P * Q) = homogeneousComponent k P * Q := by
    intro k
    conv_lhs => rw [← sum_homogeneousComponent P]
    rw [Finset.sum_mul, map_sum]
    have hterm : ∀ i, homogeneousComponent (k + b) (homogeneousComponent i P * Q)
        = if i = k then homogeneousComponent i P * Q else 0 := by
      intro i
      have hm : homogeneousComponent i P * Q ∈ homogeneousSubmodule σ ℝ (i + b) :=
        (homogeneousComponent_isHomogeneous i P).mul hQh
      rw [homogeneousComponent_of_mem hm]
      by_cases h : i = k
      · simp [h]
      · have : k + b ≠ i + b := by omega
        rw [if_neg this, if_neg h]
    simp_rw [hterm]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · subst_vars; rfl
    · simp only [Finset.mem_range, not_lt] at h
      rw [homogeneousComponent_eq_zero k P (by omega), zero_mul]
  have hzero : ∀ k, k ≠ a → homogeneousComponent k P = 0 := by
    intro k hk
    have h1 : homogeneousComponent (k + b) (P * Q) = 0 := by
      have : k + b ≠ a + b := by omega
      have e := homogeneousComponent_of_mem (m := k + b) (hPQ : P * Q ∈ homogeneousSubmodule σ ℝ (a + b))
      rw [e, if_neg this]
    rw [key] at h1
    exact (mul_eq_zero.mp h1).resolve_right hQ
  rw [← sum_homogeneousComponent P]
  apply IsHomogeneous.sum
  intro k _
  by_cases hk : k = a
  · subst hk; exact homogeneousComponent_isHomogeneous k P
  · rw [hzero k hk]; exact isHomogeneous_zero _ _ _

/- English proof (translation)
Introduce `P Q a b` and use `isHomogeneous_of_mul_isHomogeneous_right P Q a b`.
-/
example : ∀ {σ : Type} (P Q : MvPolynomial σ ℝ) (a b : ℕ), Q ≠ 0 → Q.IsHomogeneous b → (P * Q).IsHomogeneous (a + b) → P.IsHomogeneous a :=
  fun P Q a b => isHomogeneous_of_mul_isHomogeneous_right P Q a b

end GlobalTheory.GrassTop
