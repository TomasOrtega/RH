import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.prod_range_succ, ih]`. Distinguish the cases in `h : i < n`.

Take `⟨t, rfl⟩ : ∃ t, n = i + 1 + t` from `⟨n - (i + 1), by omega⟩`. Establish `e1 : i + 1 + t - 1 - i = t` using `by omega`. Establish `e2 : i + 1 + t + 1 - 1 - i = t + 1` using `by omega`. Rewrite using `[if_pos h, e1, e2, Nat.factorial_succ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `e1 : n - 1 - i = 0` using `by omega`. Establish `e2 : n + 1 - 1 - i = 0` using `by omega`. Rewrite using `[if_neg h, e1, e2]`. Simplify using the standard rewrite rules.
-/
theorem prod_range_sub_eq_factorial (i n : ℕ) :
    ∏ k ∈ Finset.range n, (if i < k then ((k : ℝ) - (i : ℝ)) else 1) = (((n - 1 - i).factorial : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    by_cases h : i < n
    · obtain ⟨t, rfl⟩ : ∃ t, n = i + 1 + t := ⟨n - (i + 1), by omega⟩
      have e1 : i + 1 + t - 1 - i = t := by omega
      have e2 : i + 1 + t + 1 - 1 - i = t + 1 := by omega
      rw [if_pos h, e1, e2, Nat.factorial_succ]
      push_cast
      ring
    · have e1 : n - 1 - i = 0 := by omega
      have e2 : n + 1 - 1 - i = 0 := by omega
      rw [if_neg h, e1, e2]
      simp

/- English proof (translation)
Rewrite using `[Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h` using `prod_range_sub_eq_factorial (i : ℕ) N`. Rewrite `h` using `[← Fin.prod_univ_eq_prod_range (fun k => if (i : ℕ) < k then ((k : ℝ) - ((i : ℕ) : ℝ)) else 1) N]`. Establish `hr : (rhoM Ψ N) (τ, i) = N - 1 - (i : ℕ)` using `rfl`.

Rewrite using `[hr, ← h]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Fin.lt_def]`.
-/
theorem prod_rhoM_factorial (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    ∏ p, (((rhoM Ψ N) p).factorial : ℝ) =
      ∏ _τ : Ψ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then ((k : ℝ) - (i : ℝ)) else 1) := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_
  have h := prod_range_sub_eq_factorial (i : ℕ) N
  rw [← Fin.prod_univ_eq_prod_range (fun k => if (i : ℕ) < k then ((k : ℝ) - ((i : ℕ) : ℝ)) else 1) N] at h
  have hr : (rhoM Ψ N) (τ, i) = N - 1 - (i : ℕ) := rfl
  rw [hr, ← h]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Fin.lt_def]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
