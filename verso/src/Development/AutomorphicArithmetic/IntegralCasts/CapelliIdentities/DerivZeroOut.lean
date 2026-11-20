import Mathlib

namespace YiaHelp

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private lemma deriv_zero_out (x : ℝ) (hx : x ∉ Set.Icc (0 : ℝ) (1 : ℝ)) :
    deriv Real.smoothTransition x = 0 := by
  rcases lt_or_ge x 0 with h | h
  · have : Real.smoothTransition =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [this.deriv_eq]; simp
  · have h1 : 1 < x := by
      by_contra hc
      exact hx ⟨h, not_lt.mp hc⟩
    have : Real.smoothTransition =ᶠ[nhds x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h1] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [this.deriv_eq]; simp

end YiaHelp

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.Yia2.main :
    ∃ (K : ℝ),
      (0 : ℝ) ≤ K ∧
        (∀ (x : ℝ), |deriv Real.smoothTransition x| ≤ K) ∧
          ∀ x ∉ Set.Icc (0 : ℝ) (1 : ℝ), deriv Real.smoothTransition x = (0 : ℝ) := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_, YiaHelp.deriv_zero_out⟩
  intro x
  by_cases hx : x ∈ Set.Icc (0 : ℝ) (1 : ℝ)
  · have := hC x hx
    rw [Real.norm_eq_abs] at this
    exact le_trans this (le_max_left _ _)
  · rw [YiaHelp.deriv_zero_out x hx]; simp
