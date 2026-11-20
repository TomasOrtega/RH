import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
