import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesGenIndexMono

/- English proof (translation)
Unfold `genIndex`. Rewrite using `[AddSubgroup.relIndex_eq_one.mpr h, Nat.cast_one, div_one]`.
-/
theorem genIndex_of_le {G : Type*} [AddCommGroup G] {A A' : AddSubgroup G} (h : A ≤ A') :
    genIndex A' A = (A.relIndex A' : ℝ) := by
  unfold genIndex
  rw [AddSubgroup.relIndex_eq_one.mpr h, Nat.cast_one, div_one]

/- English proof (translation)
Unfold `genIndex`. Check the signs of the components of the expression.
-/
theorem genIndex_nonneg {G : Type*} [AddCommGroup G] (A B : AddSubgroup G) : 0 ≤ genIndex A B := by
  unfold genIndex
  positivity

end KLinesGenIndexMono

open KLinesGenIndexMono in

/- English proof (translation)
Introduce `V _ _ _ A A' B hA hA' hB hle`. Take `⟨hpos, heq⟩` from `h1 V A' A B hA' hA hB`. Establish `hle' : A.toAddSubgroup ≤ A'.toAddSubgroup` using `hle`. Rewrite using `[← heq]`. Rewrite `hpos`, the goal using `[genIndex_of_le hle']`.

Establish `hone : (1 : ℝ) ≤ (A.toAddSubgroup.relIndex A'.toAddSubgroup : ℝ)`. Establish `: 0 < A.toAddSubgroup.relIndex A'.toAddSubgroup` using `by exact_mod_cast hpos`. Conclude with `this` after adjusting the coercions. Conclude with `le_mul_of_one_le_left (genIndex_nonneg _ _) hone`.
-/
theorem LinesGenIndexMono.proof (h1 : LinesGenIndexTrans.Statement) : LinesGenIndexMono.Statement := by
  intro V _ _ _ A A' B hA hA' hB hle
  obtain ⟨hpos, heq⟩ := h1 V A' A B hA' hA hB
  have hle' : A.toAddSubgroup ≤ A'.toAddSubgroup := hle
  rw [← heq]
  rw [genIndex_of_le hle'] at hpos ⊢
  have hone : (1 : ℝ) ≤ (A.toAddSubgroup.relIndex A'.toAddSubgroup : ℝ) := by
    have : 0 < A.toAddSubgroup.relIndex A'.toAddSubgroup := by exact_mod_cast hpos
    exact_mod_cast this
  exact le_mul_of_one_le_left (genIndex_nonneg _ _) hone

end GroundTheory.Heights₂.Heights
