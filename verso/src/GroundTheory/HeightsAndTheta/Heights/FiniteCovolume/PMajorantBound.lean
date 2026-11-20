import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix
open scoped ComplexOrder

/- English proof (translation)
Take `⟨hP, -, hdet, hPHP⟩` from `hM`. Establish `hPdet : IsUnit P.det` using `isUnit_iff_ne_zero.mpr (ne_of_gt hP.det_pos)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_nonsing_inv _ hPdet, Matrix.mul_one, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]`.
-/
theorem majorant_mul_inv_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {H P : Matrix ι ι ℂ}
    (hM : IsMajorantOf H P) : H * P⁻¹ * H = P := by
  obtain ⟨hP, -, hdet, hPHP⟩ := hM
  have hPdet : IsUnit P.det := isUnit_iff_ne_zero.mpr (ne_of_gt hP.det_pos)
  calc H * P⁻¹ * H = (P * H⁻¹ * P) * P⁻¹ * H := by rw [hPHP]
    _ = P * H⁻¹ * (P * P⁻¹) * H := by simp only [Matrix.mul_assoc]
    _ = P := by
      rw [Matrix.mul_nonsing_inv _ hPdet, Matrix.mul_one, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]

/- English proof (translation)
Introduce `H P hM z`. Establish `key` using `majorant_mul_inv_mul hM`. Take `⟨hP, hH, hdet, hPHP⟩` from `hM`. Establish `hPdet : IsUnit P.det` using `isUnit_iff_ne_zero.mpr (ne_of_gt hP.det_pos)`. Use `set w := P⁻¹ *ᵥ (H *ᵥ z) with hw`.

Establish `h1 : P *ᵥ w = H *ᵥ z`. Rewrite using `[hw, mulVec_mulVec, Matrix.mul_nonsing_inv _ hPdet, one_mulVec]`. Establish `hPinv : (P⁻¹)ᴴ = P⁻¹` using `by rw [conjTranspose_nonsing_inv, hP.1.eq]`. Establish `h2 : star w ⬝ᵥ (P *ᵥ w) = star z ⬝ᵥ (P *ᵥ z)`. Rewrite using `[h1, hw, star_mulVec, star_mulVec, hPinv, hH.eq, vecMul_vecMul, ← dotProduct_mulVec, mulVec_mulVec, key]`.

Set `_` to `P.toSeminormedAddCommGroup hP.posSemidef`. Set `_` to `P.toInnerProductSpace hP.posSemidef`. Establish `cs` using `inner_mul_inner_self_le (𝕜 := ℂ) z w`. Establish `e1 : (inner ℂ z w : ℂ) = star z ⬝ᵥ (H *ᵥ z)`. Express the relevant statement in the definitionally equal form `(P *ᵥ w) ⬝ᵥ star z = _`.

Rewrite using `[dotProduct_comm, h1]`. Establish `e2 : (inner ℂ w z : ℂ) = star (star z ⬝ᵥ (H *ᵥ z))`. Rewrite using `[← e1]`. Conclude with `(inner_conj_symm (𝕜 := ℂ) w z).symm`. Establish `e3 : (inner ℂ z z : ℂ) = star z ⬝ᵥ (P *ᵥ z)`.

Express the relevant statement in the definitionally equal form `(P *ᵥ z) ⬝ᵥ star z = _`. Rewrite using `[dotProduct_comm]`. Establish `e4 : (inner ℂ w w : ℂ) = star z ⬝ᵥ (P *ᵥ z)`. Express the relevant statement in the definitionally equal form `(P *ᵥ w) ⬝ᵥ star w = _`. Rewrite using `[dotProduct_comm, h2]`.

Rewrite `cs` using `[e1, e2, e3, e4, norm_star]`. Establish `hnn : 0 ≤ (star z ⬝ᵥ (P *ᵥ z)).re` using `hP.posSemidef.re_dotProduct_nonneg z`. Establish `hn : 0 ≤ ‖star z ⬝ᵥ (H *ᵥ z)‖` using `norm_nonneg _`. Simplify using `only [RCLike.re_to_complex] at cs`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem MajorantBound.proof (ι : Type*) [Fintype ι] [DecidableEq ι] :
    MajorantBound.Statement ι := by
  intro H P hM z
  have key := majorant_mul_inv_mul hM
  obtain ⟨hP, hH, hdet, hPHP⟩ := hM
  have hPdet : IsUnit P.det := isUnit_iff_ne_zero.mpr (ne_of_gt hP.det_pos)
  set w := P⁻¹ *ᵥ (H *ᵥ z) with hw
  have h1 : P *ᵥ w = H *ᵥ z := by
    rw [hw, mulVec_mulVec, Matrix.mul_nonsing_inv _ hPdet, one_mulVec]
  have hPinv : (P⁻¹)ᴴ = P⁻¹ := by rw [conjTranspose_nonsing_inv, hP.1.eq]
  have h2 : star w ⬝ᵥ (P *ᵥ w) = star z ⬝ᵥ (P *ᵥ z) := by
    rw [h1, hw, star_mulVec, star_mulVec, hPinv, hH.eq, vecMul_vecMul, ← dotProduct_mulVec,
      mulVec_mulVec, key]
  let _ := P.toSeminormedAddCommGroup hP.posSemidef
  let _ := P.toInnerProductSpace hP.posSemidef
  have cs := inner_mul_inner_self_le (𝕜 := ℂ) z w
  have e1 : (inner ℂ z w : ℂ) = star z ⬝ᵥ (H *ᵥ z) := by
    change (P *ᵥ w) ⬝ᵥ star z = _
    rw [dotProduct_comm, h1]
  have e2 : (inner ℂ w z : ℂ) = star (star z ⬝ᵥ (H *ᵥ z)) := by
    rw [← e1]; exact (inner_conj_symm (𝕜 := ℂ) w z).symm
  have e3 : (inner ℂ z z : ℂ) = star z ⬝ᵥ (P *ᵥ z) := by
    change (P *ᵥ z) ⬝ᵥ star z = _
    rw [dotProduct_comm]
  have e4 : (inner ℂ w w : ℂ) = star z ⬝ᵥ (P *ᵥ z) := by
    change (P *ᵥ w) ⬝ᵥ star w = _
    rw [dotProduct_comm, h2]
  rw [e1, e2, e3, e4, norm_star] at cs
  have hnn : 0 ≤ (star z ⬝ᵥ (P *ᵥ z)).re := hP.posSemidef.re_dotProduct_nonneg z
  have hn : 0 ≤ ‖star z ⬝ᵥ (H *ᵥ z)‖ := norm_nonneg _
  simp only [RCLike.re_to_complex] at cs
  nlinarith

end GroundTheory.Heights₂.Heights.FiniteCovolume
