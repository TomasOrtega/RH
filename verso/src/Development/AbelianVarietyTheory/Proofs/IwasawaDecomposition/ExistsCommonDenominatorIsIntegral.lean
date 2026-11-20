import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory

/- English proof (translation)
Take `⟨y, hy, h⟩` from `exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image f)`. Use `⟨y.natAbs, Int.natAbs_pos.mpr hy, fun j => ?_⟩` and prove the remaining obligations. Establish `hj` using `h (f j) (Finset.mem_image_of_mem f (Finset.mem_univ j))`. Rewrite `hj` using `[zsmul_eq_mul]`. Break down `Int.natAbs_eq y with e | e` into its components or cases.

Establish `: ((y.natAbs : ℕ) : E) = (y : E)` using `by conv_rhs => rw [e]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `hj`. Establish `: ((y.natAbs : ℕ) : E) = -(y : E)` using `by conv_rhs => rw [e]`.

Simplify using the standard rewrite rules. Rewrite using `[this, neg_mul]`. Conclude with `hj.neg`.
-/
theorem exists_common_denominator (E : Type) [Field E] [NumberField E] (n : ℕ) (f : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ ∀ j, IsIntegral ℤ ((d : E) * f j) := by
  classical
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image f)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, fun j => ?_⟩
  have hj := h (f j) (Finset.mem_image_of_mem f (Finset.mem_univ j))
  rw [zsmul_eq_mul] at hj
  rcases Int.natAbs_eq y with e | e
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [e]
      simp
    rw [this]; exact hj
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [e]
      simp
    rw [this, neg_mul]; exact hj.neg

end GlobalTheory
