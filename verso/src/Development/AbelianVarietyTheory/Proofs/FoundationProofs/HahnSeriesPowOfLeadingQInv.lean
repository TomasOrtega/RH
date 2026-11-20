import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Definitions.Foundations.SiegelNeZeroIff
open scoped MatrixGroups
open GlobalTheory.KZ

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hahn_pow_neg_one_lead {R : Type} [CommRing R] (x : HahnSeries ℚ R)
    (h1 : x.coeff (-1) = 1) (hlt : ∀ r : ℚ, r < -1 → x.coeff r = 0) :
    ∀ m : ℕ, (x ^ m).coeff (-(m : ℚ)) = 1 ∧ ∀ r : ℚ, r < -(m : ℚ) → (x ^ m).coeff r = 0 := by
  intro m
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨Subsingleton.elim _ _, fun r _ => Subsingleton.elim _ _⟩
  have hx0 : x ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  have hxo : x.order = -1 := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by rw [h1]; exact one_ne_zero)) ?_
    by_contra hc
    push_neg at hc
    exact hx0 (HahnSeries.coeff_order_eq_zero.mp (hlt _ hc))
  have hxl : x.leadingCoeff = 1 := by
    rw [HahnSeries.leadingCoeff_eq, hxo, h1]
  have key : ∀ n : ℕ, (x ^ n).order = -(n : ℚ) ∧ (x ^ n).leadingCoeff = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hne : (x ^ n).leadingCoeff * x.leadingCoeff ≠ 0 := by
        rw [ih.2, hxl, one_mul]; exact one_ne_zero
      rw [pow_succ, HahnSeries.order_mul_of_ne_zero hne, HahnSeries.leadingCoeff_mul_of_ne_zero hne,
        ih.1, ih.2, hxo, hxl]
      constructor
      · push_cast; ring
      · simp
  obtain ⟨ho, hl⟩ := key m
  refine ⟨?_, fun r hr => ?_⟩
  · rw [← ho, ← HahnSeries.leadingCoeff_eq, hl]
  · exact HahnSeries.coeff_eq_zero_of_lt_order (by rw [ho]; exact hr)

end GlobalTheory
