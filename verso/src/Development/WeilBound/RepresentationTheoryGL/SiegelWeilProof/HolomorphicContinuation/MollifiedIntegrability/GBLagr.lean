import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Lagr

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

/- English proof (translation)
Introduce `D`. Use `set V : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ := Matrix.vandermonde fun i => ((i : ℕ) : ℂ) with hV`. Establish `hdet : V.det ≠ 0`. Rewrite using `[hV, Matrix.det_vandermonde]`. Use `Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_` and prove the remaining obligations.

Establish `hij : i < j` using `(Finset.mem_Ioi.1 hj)`. Introduce `h`. Establish `: ((j : ℕ) : ℂ) = ((i : ℕ) : ℂ)` using `by linear_combination h`. Use `Nat.cast_injective this` as an intermediate fact. Conclude with `absurd (Fin.ext this) (ne_of_gt hij)`.

Establish `hunit : IsUnit V.det` using `isUnit_iff_ne_zero.2 hdet`. Use `set W := V⁻¹ with hW`. Use `⟨∑ j, ∑ i, ‖W j i‖, fun c B hB j hj => ?_⟩` and prove the remaining obligations. Use `set cv : Fin (D + 1) → ℂ := fun j => c j with hcv`. Establish `hvals : ∀ i : Fin (D + 1), V.mulVec cv i = ∑ j ∈ Finset.range (D + 1), (((i : ℕ) : ℕ) : ℂ) ^ j * c j`.

Introduce `i`. Simplify using `only [Matrix.mulVec, dotProduct, hV, Matrix.vandermonde_apply, hcv]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun k => ((i : ℕ) : ℂ) ^ k * c k)]`. Establish `hB' : ∀ i : Fin (D + 1), ‖V.mulVec cv i‖ ≤ B` using `fun i => by`. Rewrite using `[hvals i]`.

Conclude with `hB i (Nat.lt_succ_iff.1 i.2)`. Establish `hB0 : 0 ≤ B` using `(norm_nonneg _).trans (hB' 0)`. Establish `hinv : W.mulVec (V.mulVec cv) = cv`. Rewrite using `[Matrix.mulVec_mulVec, hW, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]`. Use `set jj : Fin (D + 1) := ⟨j, Nat.lt_succ_of_le hj⟩`.

Establish `hc : c j = ∑ i, W jj i * V.mulVec cv i`. Use `congrFun hinv jj` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, hcv] at this ⊢`. Rewrite using `[this]`. Rewrite using `[hc]`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hB' i) (norm_nonneg _)`. Use `_ = (∑ i, ‖W jj i‖) * B := by rw [Finset.sum_mul]`.

Use `_ ≤ (∑ j, ∑ i, ‖W j i‖) * B := by`. Use `mul_le_mul_of_nonneg_right ?_ hB0` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun j => ∑ i, ‖W j i‖) (fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _) (Finset.mem_univ jj)`.
-/
theorem lagr : Lagr := by
  intro D
  set V : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ := Matrix.vandermonde fun i => ((i : ℕ) : ℂ) with hV
  have hdet : V.det ≠ 0 := by
    rw [hV, Matrix.det_vandermonde]
    refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
    have hij : i < j := (Finset.mem_Ioi.1 hj)
    intro h
    have : ((j : ℕ) : ℂ) = ((i : ℕ) : ℂ) := by linear_combination h
    have := Nat.cast_injective this
    exact absurd (Fin.ext this) (ne_of_gt hij)
  have hunit : IsUnit V.det := isUnit_iff_ne_zero.2 hdet
  set W := V⁻¹ with hW
  refine ⟨∑ j, ∑ i, ‖W j i‖, fun c B hB j hj => ?_⟩
  set cv : Fin (D + 1) → ℂ := fun j => c j with hcv
  have hvals : ∀ i : Fin (D + 1), V.mulVec cv i = ∑ j ∈ Finset.range (D + 1), (((i : ℕ) : ℕ) : ℂ) ^ j * c j := by
    intro i
    simp only [Matrix.mulVec, dotProduct, hV, Matrix.vandermonde_apply, hcv]
    rw [Fin.sum_univ_eq_sum_range (fun k => ((i : ℕ) : ℂ) ^ k * c k)]
  have hB' : ∀ i : Fin (D + 1), ‖V.mulVec cv i‖ ≤ B := fun i => by
    rw [hvals i]; exact hB i (Nat.lt_succ_iff.1 i.2)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' 0)
  have hinv : W.mulVec (V.mulVec cv) = cv := by
    rw [Matrix.mulVec_mulVec, hW, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  set jj : Fin (D + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hc : c j = ∑ i, W jj i * V.mulVec cv i := by
    have := congrFun hinv jj
    simp only [Matrix.mulVec, dotProduct, hcv] at this ⊢
    rw [this]
  rw [hc]
  calc ‖∑ i, W jj i * V.mulVec cv i‖ ≤ ∑ i, ‖W jj i * V.mulVec cv i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖W jj i‖ * B := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB' i) (norm_nonneg _)
    _ = (∑ i, ‖W jj i‖) * B := by rw [Finset.sum_mul]
    _ ≤ (∑ j, ∑ i, ‖W j i‖) * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB0
        exact Finset.single_le_sum (f := fun j => ∑ i, ‖W j i‖) (fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _)
          (Finset.mem_univ jj)

end PositivityTheory.Rg.Sw.WR.K.GB
