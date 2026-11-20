import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox

namespace GlobalTheory.WeakApprox

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Evaluate the numerical expressions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem exists_integral_congr (Ω : Type) [Field Ω] (ι : Type) [Finite ι]
    (v : ι → Valuation Ω (WithZero (Multiplicative ℤ)))
    (hgen : ∀ i, ∃ x, v i x =
      ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (hind : ∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j)) (i₀ : ι) (a : Ω) (ha : v i₀ a ≤ 1) :
    ∃ a' : Ω, (∀ i, v i a' ≤ 1) ∧ v i₀ (a - a') < 1 := by
  classical
  haveI := Fintype.ofFinite ι

  have hn : ∀ i, ∃ n : ℤ, 1 ≤ n ∧
      v i a ≤ ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro i
    rcases eq_or_ne (v i a) 0 with h | h
    · exact ⟨1, le_rfl, by simp [h]⟩
    · obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp h
      refine ⟨max 1 (Multiplicative.toAdd m), le_max_left _ _, ?_⟩
      rw [← hm, WithZero.coe_le_coe]
      exact le_max_right (1 : ℤ) (Multiplicative.toAdd m)
  choose n hn1 hn2 using hn

  obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.Lift.exists_val_eq v hgen hind
    (fun i => if i = i₀ then -1 else n i)
  have ht0 : v i₀ t < 1 := by
    rw [ht i₀, if_pos rfl, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero,
      Multiplicative.ofAdd_lt]
    norm_num
  have h1t : v i₀ (1 + t) = 1 := by
    rw [(v i₀).map_add_eq_of_lt_left (by rwa [(v i₀).map_one]), (v i₀).map_one]
  have hne : 1 + t ≠ 0 := by
    intro h0
    rw [h0, (v i₀).map_zero] at h1t
    exact zero_ne_one h1t
  refine ⟨a / (1 + t), fun i => ?_, ?_⟩
  · rw [map_div₀]
    by_cases hi : i = i₀
    · subst hi
      rw [h1t, div_one]
      exact ha
    · have hti : v i t = ((Multiplicative.ofAdd (n i) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) := by
        rw [ht i, if_neg hi]
      have hlt : v i 1 < v i t := by
        rw [hti, (v i).map_one, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero,
          Multiplicative.ofAdd_lt]
        linarith [hn1 i]
      rw [(v i).map_add_eq_of_lt_right hlt, hti]
      exact div_le_one_of_le₀ (hn2 i) zero_le'
  · have hsub : a - a / (1 + t) = a * t / (1 + t) := by
      field_simp
      ring
    rw [hsub, map_div₀, h1t, div_one, map_mul]
    calc v i₀ a * v i₀ t ≤ 1 * v i₀ t := by gcongr
      _ = v i₀ t := one_mul _
      _ < 1 := ht0

end GlobalTheory.WeakApprox
