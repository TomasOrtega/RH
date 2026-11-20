import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

/- English proof (translation)
Introduce `R`. Proceed by induction on `R with`. Consider the case `zero`. Introduce `B U T hB hU hT`. Establish `hT0 : T = ∅` using `Finset.card_eq_zero.mp (by omega)`.

Substitute `hT0` using the available equality. Use `⟨U / 2, ?_, by linarith, ?_⟩` and prove the remaining obligations. Apply `div_le_div_of_nonneg_left hU.le (by norm_num)` to reduce the goal to its premises. Evaluate the numerical expressions. Introduce `a ha`.

Simplify using `at ha`. Consider the case `succ n ih`. Introduce `B U T hB hU hT`. Establish `hB0 : 0 < B` using `by linarith`. Distinguish the cases in `h : ∃ a ∈ T, U / (2 * B) < a ∧ a ≤ U`.

Take `⟨a0, ha0, h1, h2⟩` from `h`. Take `⟨y, hy1, hy2, hy3⟩` from `ih B (U / (2 * B)) (T.erase a0) hB (by positivity) (by rw [Finset.card_erase_of_mem ha0]; omega)`. Use `⟨y, ?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_div]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ y := hy1`. Establish `: U / (2 * B) ≤ U` using `div_le_self hU.le (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `a ha u hu1 hu2 hau`. Distinguish the cases in `hae : a = a0`. Substitute `hae` using the available equality. It suffices to derive a contradiction. Establish `: U / (2 * B) < u` using `lt_of_lt_of_le h1 hau`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hy3 a (Finset.mem_erase.mpr ⟨hae, ha⟩) u hu1 hu2 hau`. Use `push_neg at h`. Use `⟨U / 2, ?_, by linarith, ?_⟩` and prove the remaining obligations. Apply `div_le_div_of_nonneg_left hU.le (by norm_num)` to reduce the goal to its premises.

Establish `h2 : (1 : ℝ) ≤ 2 ^ n` using `one_le_pow₀ (by norm_num)`. Establish `h3 : (1 : ℝ) ≤ B ^ (n + 1)` using `one_le_pow₀ hB`. Establish `h4 : (2 : ℝ) ^ (n + 1 + 2) = 8 * 2 ^ n` using `by ring`. Rewrite using `[h4]`. Use the polynomial consequences of the given equalities and inequalities.

Introduce `a ha u hu1 hu2 hau`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `ha1 : U / (2 * B) < a`. Rewrite using `[div_lt_iff₀ (by positivity)]`.

Use the polynomial consequences of the given equalities and inequalities. Use `h a ha ha1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
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
