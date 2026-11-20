import Formalism.ZetaRealNonvanish

open Complex

noncomputable section

namespace Formalism

/- English proof (translation)
Use `set t : ℂ := ((2 * m + 2 : ℕ) : ℂ) with ht`. Establish `htre : t.re = 2 * (m : ℝ) + 2` using `by simp [ht]`. Establish `ht1 : (1 : ℝ) < t.re` using `by rw [htre]; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]`. Establish `hn : ∀ n : ℕ, t ≠ -n`. Introduce `n hn`.

Use `congrArg Complex.re hn` as an intermediate fact. Rewrite `this` using `[htre]`. Simplify using `at this`. Establish `h0 : (0 : ℝ) ≤ n` using `n.cast_nonneg`. Combine the linear relations using `[(m.cast_nonneg : (0 : ℝ) ≤ m)]`.

Establish `ht1' : t ≠ 1`. Introduce `h1`. Use `congrArg Complex.re h1` as an intermediate fact. Rewrite `this` using `[htre]`. Simplify using `at this`.

Combine the linear relations using `[(m.cast_nonneg : (0 : ℝ) ≤ m)]`. Establish `hfe` using `riemannZeta_one_sub hn ht1'`. Establish `hsub : (1 : ℂ) - t = -((2 * m + 1 : ℕ) : ℂ)`. Rewrite using `[ht]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hfe` using `[hsub]`. Rewrite using `[hfe]`. Establish `hcos : Complex.cos (Real.pi * t / 2) = ((Real.cos (((m + 1 : ℕ) : ℝ) * Real.pi) : ℝ) : ℂ)`. Rewrite using `[ht]`.

Use `push_cast`. Put the polynomial expressions in normal form. Establish `hpi : (2 * ((Real.pi : ℝ) : ℂ)) ≠ 0`. Establish `: (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Conclude with `mul_ne_zero two_ne_zero this`.

Use `mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_) (riemannZeta_ne_zero_of_one_lt_re ht1)` and prove the remaining obligations. Conclude with `(cpow_ne_zero_iff).mpr (Or.inl hpi)`. Conclude with `Complex.Gamma_ne_zero hn`. Rewrite using `[hcos, Real.cos_nat_mul_pi]`. Use `push_cast`.

Conclude with `pow_ne_zero _ (by norm_num)`.
-/
lemma zeta_neg_odd_ne_zero (m : ℕ) : riemannZeta (-((2 * m + 1 : ℕ) : ℂ)) ≠ 0 := by
  set t : ℂ := ((2 * m + 2 : ℕ) : ℂ) with ht
  have htre : t.re = 2 * (m : ℝ) + 2 := by simp [ht]
  have ht1 : (1 : ℝ) < t.re := by rw [htre]; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hn : ∀ n : ℕ, t ≠ -n := by
    intro n hn
    have := congrArg Complex.re hn
    rw [htre] at this
    simp at this
    have h0 : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have ht1' : t ≠ 1 := by
    intro h1
    have := congrArg Complex.re h1
    rw [htre] at this
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hfe := riemannZeta_one_sub hn ht1'
  have hsub : (1 : ℂ) - t = -((2 * m + 1 : ℕ) : ℂ) := by
    rw [ht]; push_cast; ring
  rw [hsub] at hfe
  rw [hfe]
  have hcos : Complex.cos (Real.pi * t / 2) = ((Real.cos (((m + 1 : ℕ) : ℝ) * Real.pi) : ℝ) : ℂ) := by
    rw [ht]; push_cast; ring_nf
  have hpi : (2 * ((Real.pi : ℝ) : ℂ)) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_)
    (riemannZeta_ne_zero_of_one_lt_re ht1)
  · exact (cpow_ne_zero_iff).mpr (Or.inl hpi)
  · exact Complex.Gamma_ne_zero hn
  · rw [hcos, Real.cos_nat_mul_pi]
    push_cast
    exact pow_ne_zero _ (by norm_num)

/- English proof (translation)
Introduce `h s hs htriv hs1`. Assume the negation of the conclusion as `hne`. Break down `lt_or_gt_of_ne hne with hlt | hgt` into its components or cases. Distinguish the cases in `hn : ∃ n : ℕ, s = -n`. Take `⟨n, rfl⟩` from `hn`.

Take `⟨k, rfl | rfl⟩` from `Nat.even_or_odd' n`. Break down `k with _ | m` into its components or cases. Simplify using `[riemannZeta_zero] at hs`. Conclude with `htriv ⟨m, by push_cast; ring⟩`. Conclude with `zeta_neg_odd_ne_zero k hs`.

Simplify using `only [not_exists] at hn`. Establish `hfe` using `riemannZeta_one_sub hn hs1`. Rewrite `hfe` using `[hs, mul_zero]`. Conclude with `h (1 - s) (by simp; linarith) hfe`. Conclude with `h s hgt hs`.
-/
theorem riemannHypothesis_of_zero_free_halfPlane : RHofHalfPlane := by
  intro h s hs htriv hs1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · by_cases hn : ∃ n : ℕ, s = -n
    · obtain ⟨n, rfl⟩ := hn
      obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
      · rcases k with _ | m
        · simp [riemannZeta_zero] at hs
        · exact htriv ⟨m, by push_cast; ring⟩
      · exact zeta_neg_odd_ne_zero k hs
    · simp only [not_exists] at hn
      have hfe := riemannZeta_one_sub hn hs1
      rw [hs, mul_zero] at hfe
      exact h (1 - s) (by simp; linarith) hfe
  · exact h s hgt hs

end Formalism
