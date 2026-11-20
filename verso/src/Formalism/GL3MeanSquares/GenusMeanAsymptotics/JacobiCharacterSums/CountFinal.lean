import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountSt
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountA
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis
import Formalism.GL3MeanSquares.HookFormulaTorsion.TwistIsPrimitiveCharacter

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts

open DirichletCharacter

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Apply the first step, then apply the next step to every resulting obligation. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Rewrite the indicated hypotheses using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem boxCountHyp_of_zeroDensityBox (h : ZeroDensityBox) : ∃ C : ℝ, Formalism.HermitianLattices.ZeroFreeRegionGL2.BoxCountHyp C := by
  obtain ⟨C₀, hC₀⟩ := h
  refine ⟨max C₀ 0, ?_⟩
  intro t _ θ Q S hθ hθ2 hS
  by_cases hSe : S = ∅
  · subst hSe
    simp only [Finset.card_empty, Nat.cast_zero]
    apply mul_nonneg (le_max_right _ _)
    rcases le_or_gt 0 Q with hQ | hQ
    · exact Real.rpow_nonneg hQ _
    · rw [Real.rpow_def_of_neg hQ]
      apply mul_nonneg (Real.exp_pos _).le
      apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> nlinarith [Real.pi_pos]
  obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.2 hSe
  have htpos : 1 ≤ t := Nat.one_le_iff_ne_zero.2 (NeZero.ne t)
  have hQ3 : (3 : ℝ) ≤ Q := by
    obtain ⟨_, h4, _, hle, _⟩ := hS q₀ hq₀
    have hq3 : 3 ≤ q₀ := by omega
    have : 3 ≤ t * q₀ := le_trans hq3 (Nat.le_mul_of_pos_left _ htpos)
    have h3 : (3 : ℝ) ≤ ((t * q₀ : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  classical
  let f : ℕ → Σ N : ℕ, DirichletCharacter ℂ (N + 1) := fun q =>
    if hq : q.Prime then
      haveI : Fact q.Prime := ⟨hq⟩
      toSig (Formalism.HermitianLattices.ZeroFreeRegionGL2.tw θ q)
    else ⟨0, 1⟩
  have hf : ∀ q (hq : Fact q.Prime), f q = toSig (Formalism.HermitianLattices.ZeroFreeRegionGL2.tw θ q) := by
    intro q hq
    simp only [f, dif_pos hq.out]
  have hinj : Set.InjOn f S := by
    intro a ha b hb hab
    obtain ⟨ia, -⟩ := hS a ha
    obtain ⟨ib, -⟩ := hS b hb
    rw [hf a ia, hf b ib] at hab
    have := toSig_level_eq _ _ hab
    exact Nat.eq_of_mul_eq_mul_left htpos this
  have hcard : (S.image f).card = S.card := Finset.card_image_of_injOn hinj
  have key := hC₀ Q (S.image f) hQ3 (by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨iq, h4, hco, hle, hbox⟩ := hS q hq
    rw [hf q iq]
    refine ⟨?_, ?_, ?_⟩
    · rw [toSig_isPrimitive]
      exact (Formalism.HermitianLattices.ThinSetIntegral.twist_is_primitive_character.2 t θ q hθ (by omega) hco).1
    · rw [toSig_fst]; exact hle
    · unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.ZeroFreeBox at hbox
      push Not at hbox
      obtain ⟨s, h1, h2, h3⟩ := hbox
      exact ⟨s, h1, h2, by rw [toSig_LFunction]; exact h3⟩)
  rw [hcard] at key
  calc (S.card : ℝ) ≤ C₀ * Q ^ (1 / 4 : ℝ) := key
    _ ≤ max C₀ 0 * Q ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
