import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StConeVanishingHomog
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartZeroSet
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Finset

/- English proof (translation)
Introduce `n C hC f hf d`. Rewrite `hf`, the goal using `[mem_vanishingIdeal_iff]`. Introduce `c hc`. Use `replace hf : ∀ x ∈ C, eval x f = 0 := hf`. Use `show eval c (homogeneousComponent d f) = 0`.

Use `set p : Polynomial ℂ := ∑ i ∈ range (f.totalDegree + 1), Polynomial.C (eval c (homogeneousComponent i f)) * Polynomial.X ^ i with hp`. Establish `hroot : ∀ a : ℂ, a ≠ 0 → p.IsRoot a`. Introduce `a ha`. Establish `h0` using `hf (a • c) (hC c hc a ha)`. Rewrite `h0` using `[← sum_homogeneousComponent f, map_sum]`.

Rewrite using `[Polynomial.IsRoot, hp, Polynomial.eval_finsetSum, ← h0]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[GoodChartZeroSet.eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous i f)]`. Rewrite using `[Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]`. Establish `hinf : Set.Infinite {x | p.IsRoot x}`.

Use `Set.Infinite.mono (fun x hx => hroot x hx) ?_` and prove the remaining obligations. Conclude with `(Set.finite_singleton (0 : ℂ)).infinite_compl`. Establish `hp0 : p = 0` using `Polynomial.eq_zero_of_infinite_isRoot p hinf`. Distinguish the cases in `hd : d ≤ f.totalDegree`. Establish `hcoeff` using `congrArg (fun q : Polynomial ℂ => q.coeff d) hp0`.

Simplify using `only [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hcoeff`. Rewrite `hcoeff` using `[Finset.sum_ite_eq]`. Simplify `hcoeff` using `[Finset.mem_range, Nat.lt_succ_of_le hd]`. Rewrite using `[homogeneousComponent_eq_zero d f (by omega), map_zero]`.
-/
theorem ConeVanishingHomog.proof : ConeVanishingHomog.Statement := by
  intro n C hC f hf d
  rw [mem_vanishingIdeal_iff] at hf ⊢
  intro c hc
  replace hf : ∀ x ∈ C, eval x f = 0 := hf
  show eval c (homogeneousComponent d f) = 0

  set p : Polynomial ℂ := ∑ i ∈ range (f.totalDegree + 1),
    Polynomial.C (eval c (homogeneousComponent i f)) * Polynomial.X ^ i with hp
  have hroot : ∀ a : ℂ, a ≠ 0 → p.IsRoot a := by
    intro a ha
    have h0 := hf (a • c) (hC c hc a ha)
    rw [← sum_homogeneousComponent f, map_sum] at h0
    rw [Polynomial.IsRoot, hp, Polynomial.eval_finsetSum, ← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GoodChartZeroSet.eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous i f)]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  have hinf : Set.Infinite {x | p.IsRoot x} := by
    refine Set.Infinite.mono (fun x hx => hroot x hx) ?_
    exact (Set.finite_singleton (0 : ℂ)).infinite_compl
  have hp0 : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p hinf
  by_cases hd : d ≤ f.totalDegree
  · have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff d) hp0
    simp only [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hcoeff
    rw [Finset.sum_ite_eq] at hcoeff
    simpa [Finset.mem_range, Nat.lt_succ_of_le hd] using hcoeff
  · rw [homogeneousComponent_eq_zero d f (by omega), map_zero]

end GroundTheory.Heights₂.Heights
