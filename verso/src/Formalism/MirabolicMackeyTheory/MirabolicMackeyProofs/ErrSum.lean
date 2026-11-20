import Mathlib
import Formalism.MirabolicMackeyTheory.StatementT

namespace Formalism.EigenvalueLevelCeiling

/- English proof (translation)
Introduce `PI hPI Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hPS`. Take `⟨h1, h2, h3, h4, h5⟩` from `hPS`. Take `⟨Q, hQ⟩ : ∃ Q, Q = PI.filter (fun p : ℕ => (p : ℝ) ≤ Y)` from `⟨_, rfl⟩`. Establish `hQp : ∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y`. Introduce `p hp`.

Rewrite `hp` using `[hQ]`. Conclude with `⟨hPI p (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩`. Establish `e1 : ∑ p ∈ PI, Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p = ∑ p ∈ Q, 2 * (A1 * (Real.log (p : ℝ) / (p : ℝ)) + kw * (th p * Real.log (p : ℝ)) + T * (add p * Real.log (p : ℝ)) + A2 * (if X2 < (p : ℝ) then Real.log (p : ℝ) / (p : ℝ) ^ 2 else 0) + Real.log (p : ℝ))`. Rewrite using `[hQ, Finset.sum_filter]`. Use `Finset.sum_congr rfl (fun p _ => ?_)` and prove the remaining obligations.

Unfold `errGood`. Distinguish the cases in `hp : (p : ℝ) ≤ Y`. Rewrite using `[if_pos hp, if_pos hp]`. Distinguish the cases in `hx : X2 < (p : ℝ)`. Rewrite using `[if_pos hx, if_pos hx]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hx, if_neg hx]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hp, if_neg hp]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2 : ∑ p ∈ Q, 2 * (A1 * (Real.log (p : ℝ) / (p : ℝ)) + kw * (th p * Real.log (p : ℝ)) + T * (add p * Real.log (p : ℝ)) + A2 * (if X2 < (p : ℝ) then Real.log (p : ℝ) / (p : ℝ) ^ 2 else 0) + Real.log (p : ℝ)) = 2 * (A1 * ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) + kw * ∑ p ∈ Q, th p * Re …`. Rewrite using `[Finset.sum_filter, ← Finset.mul_sum]`. Use `congr 1`. Simplify using `only [Finset.sum_add_distrib, Finset.mul_sum]`. Rewrite using `[e1, e2]`.

Establish `b1` using `mul_le_mul_of_nonneg_left (h1 Q hQp) hA1`. Establish `b2` using `mul_le_mul_of_nonneg_left (h4 Q (fun p hp => (hQp p hp).1)) hkw`. Establish `b3` using `h5 Q (fun p hp => (hQp p hp).1)`. Establish `b4` using `mul_le_mul_of_nonneg_left (h3 (Q.filter (fun p : ℕ => X2 < (p : ℝ))) (fun p hp => ⟨(hQp p (Finset.mem_filter.mp hp).1).1, (Finset.mem_filter.mp hp).2⟩)) hA2`. Establish `b5` using `h2 Q hQp`.

Establish `e3 : A2 * (2.04 / X2) = 2.04 * A2 / X2` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem error_sum_good_places : ErrSumGood := by
  classical
  intro PI hPI Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hPS
  obtain ⟨h1, h2, h3, h4, h5⟩ := hPS
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = PI.filter (fun p : ℕ => (p : ℝ) ≤ Y) := ⟨_, rfl⟩
  have hQp : ∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y := by
    intro p hp
    rw [hQ] at hp
    exact ⟨hPI p (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
  have e1 : ∑ p ∈ PI, Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p =
      ∑ p ∈ Q, 2 * (A1 * (Real.log (p : ℝ) / (p : ℝ)) + kw * (th p * Real.log (p : ℝ)) +
        T * (add p * Real.log (p : ℝ)) +
        A2 * (if X2 < (p : ℝ) then Real.log (p : ℝ) / (p : ℝ) ^ 2 else 0) + Real.log (p : ℝ)) := by
    rw [hQ, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    unfold errGood
    by_cases hp : (p : ℝ) ≤ Y
    · rw [if_pos hp, if_pos hp]
      by_cases hx : X2 < (p : ℝ)
      · rw [if_pos hx, if_pos hx]; ring
      · rw [if_neg hx, if_neg hx]; ring
    · rw [if_neg hp, if_neg hp]; ring
  have e2 : ∑ p ∈ Q, 2 * (A1 * (Real.log (p : ℝ) / (p : ℝ)) + kw * (th p * Real.log (p : ℝ)) +
        T * (add p * Real.log (p : ℝ)) +
        A2 * (if X2 < (p : ℝ) then Real.log (p : ℝ) / (p : ℝ) ^ 2 else 0) + Real.log (p : ℝ)) =
      2 * (A1 * ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) + kw * ∑ p ∈ Q, th p * Real.log (p : ℝ) +
        T * ∑ p ∈ Q, add p * Real.log (p : ℝ) +
        A2 * ∑ p ∈ Q.filter (fun p : ℕ => X2 < (p : ℝ)), Real.log (p : ℝ) / (p : ℝ) ^ 2 +
        ∑ p ∈ Q, Real.log (p : ℝ)) := by
    rw [Finset.sum_filter, ← Finset.mul_sum]
    congr 1
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [e1, e2]
  have b1 := mul_le_mul_of_nonneg_left (h1 Q hQp) hA1
  have b2 := mul_le_mul_of_nonneg_left (h4 Q (fun p hp => (hQp p hp).1)) hkw
  have b3 := h5 Q (fun p hp => (hQp p hp).1)
  have b4 := mul_le_mul_of_nonneg_left (h3 (Q.filter (fun p : ℕ => X2 < (p : ℝ)))
    (fun p hp => ⟨(hQp p (Finset.mem_filter.mp hp).1).1, (Finset.mem_filter.mp hp).2⟩)) hA2
  have b5 := h2 Q hQp
  have e3 : A2 * (2.04 / X2) = 2.04 * A2 / X2 := by ring
  linarith

end Formalism.EigenvalueLevelCeiling
