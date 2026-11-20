import Mathlib

namespace GlobalTheory

open Matrix in

/- English proof (translation)
Introduce `r S G hS hG`. Take `⟨m, v, rfl⟩` from `Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hG`. Establish `key : ∑ i, ∑ j, S i j * (∑ k, vecMulVec (v k) (star (v k))) i j = ∑ k, star (v k) ⬝ᵥ (S *ᵥ v k)`. Simplify using `only [Matrix.sum_apply, Finset.sum_apply, vecMulVec_apply, Pi.star_apply, star_trivial, dotProduct, mulVec, Finset.mul_sum]`. Use `conv_rhs => rw [Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `term : ∀ k, 0 ≤ star (v k) ⬝ᵥ (S *ᵥ v k)` using `fun k => hS.posSemidef.dotProduct_mulVec_nonneg _`. Rewrite using `[key]`. Use `⟨Finset.sum_nonneg fun k _ => term k, fun hne => ?_⟩` and prove the remaining obligations. Establish `: ∃ k, v k ≠ 0`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Apply `hne` to reduce the goal to its premises. Simplify using `[h]`. Take `⟨k, hk⟩` from `this`. Conclude with `Finset.sum_pos' (fun k _ => term k) ⟨k, Finset.mem_univ _, hS.dotProduct_mulVec_pos hk⟩`.
-/
theorem sum_hadamard_posDef_posSemidef :
    ∀ {r : ℕ} (S G : Matrix (Fin r) (Fin r) ℝ), S.PosDef → G.PosSemidef →
      0 ≤ ∑ i, ∑ j, S i j * G i j ∧ (G ≠ 0 → 0 < ∑ i, ∑ j, S i j * G i j) := by
  intro r S G hS hG
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hG
  have key : ∑ i, ∑ j, S i j * (∑ k, vecMulVec (v k) (star (v k))) i j
      = ∑ k, star (v k) ⬝ᵥ (S *ᵥ v k) := by
    simp only [Matrix.sum_apply, Finset.sum_apply, vecMulVec_apply, Pi.star_apply, star_trivial, dotProduct,
      mulVec, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have term : ∀ k, 0 ≤ star (v k) ⬝ᵥ (S *ᵥ v k) := fun k =>
    hS.posSemidef.dotProduct_mulVec_nonneg _
  rw [key]
  refine ⟨Finset.sum_nonneg fun k _ => term k, fun hne => ?_⟩
  have : ∃ k, v k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    simp [h]
  obtain ⟨k, hk⟩ := this
  exact Finset.sum_pos' (fun k _ => term k) ⟨k, Finset.mem_univ _, hS.dotProduct_mulVec_pos hk⟩

end GlobalTheory
