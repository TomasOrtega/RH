import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Evaluate the numerical expressions. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Substitute using the available equality. It suffices to derive a contradiction. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Win.window1 :
    ∀ (R : ℕ) (B U : ℝ) (T : Finset ℝ), 1 ≤ B → 0 < U → T.card ≤ R →
      ∃ y : ℝ, U / (2 ^ (R + 2) * B ^ R) ≤ y ∧ 2 * y ≤ U ∧ ∀ a ∈ T, ∀ u : ℝ, y ≤ u → u ≤ 2 * y → a ≤ u → B * a ≤ u := by
  intro R
  induction R with
  | zero =>
    intro B U T hB hU hT
    have hT0 : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT0
    refine ⟨U / 2, ?_, by linarith, ?_⟩
    · apply div_le_div_of_nonneg_left hU.le (by norm_num)
      norm_num
    · intro a ha
      simp at ha
  | succ n ih =>
    intro B U T hB hU hT
    have hB0 : 0 < B := by linarith
    by_cases h : ∃ a ∈ T, U / (2 * B) < a ∧ a ≤ U
    · obtain ⟨a0, ha0, h1, h2⟩ := h
      obtain ⟨y, hy1, hy2, hy3⟩ := ih B (U / (2 * B)) (T.erase a0) hB (by positivity)
        (by rw [Finset.card_erase_of_mem ha0]; omega)
      refine ⟨y, ?_, ?_, ?_⟩
      · calc U / (2 ^ (n + 1 + 2) * B ^ (n + 1))
            = U / (2 * B) / (2 ^ (n + 2) * B ^ n) := by
              rw [div_div]
              congr 1
              ring
          _ ≤ y := hy1
      · have : U / (2 * B) ≤ U := div_le_self hU.le (by linarith)
        linarith
      · intro a ha u hu1 hu2 hau
        by_cases hae : a = a0
        · subst hae
          exfalso
          have : U / (2 * B) < u := lt_of_lt_of_le h1 hau
          linarith
        · exact hy3 a (Finset.mem_erase.mpr ⟨hae, ha⟩) u hu1 hu2 hau
    · push_neg at h
      refine ⟨U / 2, ?_, by linarith, ?_⟩
      · apply div_le_div_of_nonneg_left hU.le (by norm_num)
        have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        have h3 : (1 : ℝ) ≤ B ^ (n + 1) := one_le_pow₀ hB
        have h4 : (2 : ℝ) ^ (n + 1 + 2) = 8 * 2 ^ n := by ring
        rw [h4]
        nlinarith
      · intro a ha u hu1 hu2 hau
        by_contra hc
        push_neg at hc
        have ha1 : U / (2 * B) < a := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
        have := h a ha ha1
        linarith
