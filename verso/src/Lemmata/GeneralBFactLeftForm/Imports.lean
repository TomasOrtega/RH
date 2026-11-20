import Mathlib

open Module Submodule
universe u v w

namespace Bl.general_b_fact_left_form

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem goal1 {n : ℕ} (f : Fin n → ℝ) (hf : Antitone f) (θ : ℝ) (j : Fin n) :
    θ ≤ f j ↔ (j : ℕ) < (Finset.univ.filter (fun i => θ ≤ f i)).card := by
  constructor
  · intro h
    have hsub : Finset.Iic j ⊆ Finset.univ.filter (fun i => θ ≤ f i) := by
      intro i hi
      rw [Finset.mem_Iic] at hi
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, le_trans h (hf hi)⟩
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro h
    by_contra hn0
    have hn := not_le.mp hn0
    have hsub : Finset.univ.filter (fun i => θ ≤ f i) ⊆ Finset.Iio j := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_Iio]
      by_contra hji0
      have hji := not_lt.mp hji0
      exact absurd (lt_of_le_of_lt (hf hji) hn) (not_lt.mpr hi.2)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

end Bl.general_b_fact_left_form
