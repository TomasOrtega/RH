import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableToGLEntry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentLowerRowsLeviSetClosedSubgroupStatement
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW

/- English proof (translation)
Introduce `n ρ g hg`. Prove the components needed by the constructor for the conclusion. Introduce `u hu`. Take `⟨hu0, hu1⟩` from `(GlobalTheory.SmGL.mem_unipB ℂ).1 hu`. Use function extensionality and compare the values at `j`.

Unfold `rowCut`. Use `split_ifs with hj`. Rewrite using `[Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single ρ]`. Rewrite using `[hu1, one_mul]`. Introduce `k _ hk`.

Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[hu0 ρ k h, zero_mul]`. Establish `h'` using `Fin.lt_def.1 h`. Rewrite using `[(hg k (by omega)).1 j (lt_of_le_of_lt hj h), mul_zero]`. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Assume the negation of the conclusion as `hne push_neg at hne`. Establish `hinv` using `(GlobalTheory.T.unipotentLowerRowsLeviSet_closed_subgroup n (ρ + 1)).2.1 g hg`. Establish `h1 : ((g * g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ρ ρ = 1` using `by simp`. Rewrite `h1` using `[Units.val_mul, Matrix.mul_apply, Finset.sum_eq_zero]`.

Conclude with `zero_ne_one h1`. Introduce `k _`. Distinguish the cases in `hk : k ≤ ρ`. Use `hne k hk` as an intermediate fact. Simplify using `only [rowCut, hk, if_true] at this`.

Rewrite using `[this, zero_mul]`. Use `push_neg at hk`. Establish `h'` using `Fin.lt_def.1 hk`. Rewrite using `[(hinv k (by omega)).1 ρ hk, mul_zero]`.
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
