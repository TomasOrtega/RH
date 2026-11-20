import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableToGLEntry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentLowerRowsLeviSetClosedSubgroupStatement
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Apply function extensionality and compare values at an arbitrary argument.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem truncatedRow_unipotent_mul_and_ne_zero : ∀ (n : ℕ) (ρ : Fin n), ∀ g ∈ levSet n (ρ + 1),
    (∀ u ∈ GlobalTheory.SmGL.unipB ℂ (Fin n), rowCut ρ ((u * g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ)) ∧
    ∃ j, j ≤ ρ ∧ rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ) j ≠ 0 := by
  intro n ρ g hg
  constructor
  · intro u hu
    obtain ⟨hu0, hu1⟩ := (GlobalTheory.SmGL.mem_unipB ℂ).1 hu
    funext j
    unfold rowCut
    split_ifs with hj
    · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single ρ]
      · rw [hu1, one_mul]
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h | h
        · rw [hu0 ρ k h, zero_mul]
        · have h' := Fin.lt_def.1 h
          rw [(hg k (by omega)).1 j (lt_of_le_of_lt hj h), mul_zero]
      · simp
    · rfl
  · by_contra hne
    push_neg at hne
    have hinv := (GlobalTheory.T.unipotentLowerRowsLeviSet_closed_subgroup n (ρ + 1)).2.1 g hg
    have h1 : ((g * g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ρ ρ = 1 := by simp
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      by_cases hk : k ≤ ρ
      · have := hne k hk
        simp only [rowCut, hk, if_true] at this
        rw [this, zero_mul]
      · push_neg at hk
        have h' := Fin.lt_def.1 hk
        rw [(hinv k (by omega)).1 ρ hk, mul_zero]

end GlobalTheory.JSW
