import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix
open scoped ComplexOrder

/- English proof (translation)
Introduce `H P hMaj a b ha hb`. Take `⟨hP, hH, hdet, -⟩` from `hMaj`. Establish `hHA : ∀ v : ι → ℂ, H *ᵥ (majInvolution H P *ᵥ v) = P *ᵥ v`. Introduce `v`. Rewrite using `[majInvolution, mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.one_mul]`.

Establish `hmove : ∀ (M : Matrix ι ι ℂ), M.IsHermitian → ∀ u w : ι → ℂ, star u ⬝ᵥ (M *ᵥ w) = star (M *ᵥ u) ⬝ᵥ w`. Introduce `M hM u w`. Rewrite using `[star_mulVec, hM.eq, dotProduct_mulVec]`. Establish `hPa : P *ᵥ a = H *ᵥ a` using `by rw [← hHA a, ha]`. Establish `hPb : P *ᵥ b = -(H *ᵥ b)` using `by rw [← hHA b, hb, mulVec_neg]`.

Establish `h1 : star a ⬝ᵥ (P *ᵥ b) = star a ⬝ᵥ (H *ᵥ b)`. Rewrite using `[hmove P hP.isHermitian, hPa, ← hmove H hH]`. Establish `h2 : star a ⬝ᵥ (P *ᵥ b) = -(star a ⬝ᵥ (H *ᵥ b))`. Rewrite using `[hPb, dotProduct_neg]`. Establish `h3 : (2 : ℂ) * (star a ⬝ᵥ (P *ᵥ b)) = 0`.

Rewrite using `[two_mul]`. Use `nth_rewrite 1 [h1]`. Rewrite using `[h2, add_neg_cancel]`. Simplify using `using h3`.
-/
theorem EigenspacesOrthogonal.proof (ι : Type*) [Fintype ι] [DecidableEq ι] :
    EigenspacesOrthogonal.Statement ι := by
  intro H P hMaj a b ha hb
  obtain ⟨hP, hH, hdet, -⟩ := hMaj

  have hHA : ∀ v : ι → ℂ, H *ᵥ (majInvolution H P *ᵥ v) = P *ᵥ v := by
    intro v
    rw [majInvolution, mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.one_mul]

  have hmove : ∀ (M : Matrix ι ι ℂ), M.IsHermitian → ∀ u w : ι → ℂ,
      star u ⬝ᵥ (M *ᵥ w) = star (M *ᵥ u) ⬝ᵥ w := by
    intro M hM u w
    rw [star_mulVec, hM.eq, dotProduct_mulVec]
  have hPa : P *ᵥ a = H *ᵥ a := by rw [← hHA a, ha]
  have hPb : P *ᵥ b = -(H *ᵥ b) := by rw [← hHA b, hb, mulVec_neg]
  have h1 : star a ⬝ᵥ (P *ᵥ b) = star a ⬝ᵥ (H *ᵥ b) := by
    rw [hmove P hP.isHermitian, hPa, ← hmove H hH]
  have h2 : star a ⬝ᵥ (P *ᵥ b) = -(star a ⬝ᵥ (H *ᵥ b)) := by
    rw [hPb, dotProduct_neg]
  have h3 : (2 : ℂ) * (star a ⬝ᵥ (P *ᵥ b)) = 0 := by
    rw [two_mul]
    nth_rewrite 1 [h1]
    rw [h2, add_neg_cancel]
  simpa using h3

end GroundTheory.Heights₂.Heights.FiniteCovolume
