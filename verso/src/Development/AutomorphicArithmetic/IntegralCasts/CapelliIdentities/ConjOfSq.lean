import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.Reformulated.B.Qh56.conj_of_sq :
    ∀ {w : ℂ} {q : ℕ},
    (0 : ℕ) < q → w ^ (2 : ℕ) = (↑q : ℂ) → (starRingEnd ℂ : ℂ → ℂ) w = w := by
  intro w q _ h
  have hs : ((Real.sqrt q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg q), Complex.ofReal_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (h.trans hs.symm) with hw | hw
  · rw [hw, Complex.conj_ofReal]
  · rw [hw, map_neg, Complex.conj_ofReal]
