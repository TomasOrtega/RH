import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

/- English proof (translation)
Unfold `vandermondeOf`. Use `Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_` and prove the remaining obligations. Establish `hij : i ≠ j` using `ne_of_lt (Finset.mem_Ioi.mp hj)`. Use `sub_ne_zero.mpr fun h => hij ?_` and prove the remaining obligations. Conclude with `X_injective (R := ℚ) h`.
-/
theorem vandermondeOf_X_fin_ne_zero (r : ℕ) :
    vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) ≠ 0 := by
  unfold vandermondeOf
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
  refine sub_ne_zero.mpr fun h => hij ?_
  exact X_injective (R := ℚ) h

/- English proof (translation)
Establish `h` using `IsHomogeneous.prod (σ := Fin r) (R := ℚ) Finset.univ (fun i : Fin r => ∏ j ∈ Finset.Ioi i, ((X i : MvPolynomial (Fin r) ℚ) - X j)) (fun i => ∑ _j ∈ Finset.Ioi i, 1) (fun i _ => IsHomogeneous.prod _ _ _ fun j _ => (isHomogeneous_X ℚ i).sub (isHomogeneous_X ℚ j))`. Establish `hdeg : ∑ i : Fin r, ∑ _j ∈ Finset.Ioi i, (1 : ℕ) = r * (r - 1) / 2`. Simplify using `only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Ioi]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => r - 1 - i) r, ← Finset.sum_range_id]`. Conclude with `Finset.sum_range_reflect (fun i => i) r`.

Rewrite `h` using `[hdeg]`. Conclude with `h`.
-/
theorem vandermondeOf_X_isHomogeneous (r : ℕ) :
    (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ))).IsHomogeneous
      (r * (r - 1) / 2) := by
  have h := IsHomogeneous.prod (σ := Fin r) (R := ℚ) Finset.univ
    (fun i : Fin r => ∏ j ∈ Finset.Ioi i, ((X i : MvPolynomial (Fin r) ℚ) - X j))
    (fun i => ∑ _j ∈ Finset.Ioi i, 1)
    (fun i _ => IsHomogeneous.prod _ _ _ fun j _ =>
      (isHomogeneous_X ℚ i).sub (isHomogeneous_X ℚ j))
  have hdeg : ∑ i : Fin r, ∑ _j ∈ Finset.Ioi i, (1 : ℕ) = r * (r - 1) / 2 := by
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Ioi]
    rw [Fin.sum_univ_eq_sum_range (fun i => r - 1 - i) r, ← Finset.sum_range_id]
    exact Finset.sum_range_reflect (fun i => i) r
  rw [hdeg] at h
  exact h

/- English proof (translation)
Unfold `psum`. Conclude with `IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i q`.
-/
theorem psum_isHomogeneous (σ : Type*) [Fintype σ] (q : ℕ) :
    (psum σ ℚ q).IsHomogeneous q := by
  unfold psum
  exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i q

/- English proof (translation)
Introduce `r q m _hq`. Use `set V := vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) with hVdef`. Use `set S := psum (Fin r) ℚ q * psum (Fin r) ℚ 1 ^ m with hSdef`. Establish `hprod : ((q :: List.replicate m 1).map fun k => psum (Fin r) ℚ k).prod = S`. Simplify using `[S, List.map_replicate, List.prod_replicate]`.

Establish `halt : Comb.IsAlt (V * S)`. Use `Comb.isAlt_vandermonde_mul_prod (m := r) (q :: List.replicate m 1)` as an intermediate fact. Rewrite `this` using `[hprod]`. Then use the resulting hypothesis. Establish `hhom : (V * S).IsHomogeneous (r * (r - 1) / 2 + (q + m))`. Establish `h` using `(vandermondeOf_X_isHomogeneous r).mul ((psum_isHomogeneous (Fin r) q).mul ((psum_isHomogeneous (Fin r) 1).pow m))`.

Rewrite `h` using `[one_mul]`. Then use the resulting hypothesis. Establish `hexp` using `h1 r (q + m) (V * S) halt hhom`. Apply `mul_left_cancel₀ (vandermondeOf_X_fin_ne_zero r)` to reduce the goal to its premises. Rewrite using `[Finset.mul_sum]`. Use `hexp.trans (Finset.sum_congr rfl fun lam _ => ?_)` and prove the remaining obligations.

Simplify using `only [symmetricGroupCharacter, hprod]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem FrobeniusCharacterFormula.proof (h1 : SchAltPartitionExpansion.Statement) :
    FrobeniusCharacterFormula.Statement := by
  intro r q m _hq
  set V := vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) with hVdef
  set S := psum (Fin r) ℚ q * psum (Fin r) ℚ 1 ^ m with hSdef
  have hprod : ((q :: List.replicate m 1).map fun k => psum (Fin r) ℚ k).prod = S := by
    simp [S, List.map_replicate, List.prod_replicate]
  have halt : Comb.IsAlt (V * S) := by
    have := Comb.isAlt_vandermonde_mul_prod (m := r) (q :: List.replicate m 1)
    rwa [hprod] at this
  have hhom : (V * S).IsHomogeneous (r * (r - 1) / 2 + (q + m)) := by
    have h := (vandermondeOf_X_isHomogeneous r).mul
      ((psum_isHomogeneous (Fin r) q).mul ((psum_isHomogeneous (Fin r) 1).pow m))
    rwa [one_mul] at h
  have hexp := h1 r (q + m) (V * S) halt hhom
  apply mul_left_cancel₀ (vandermondeOf_X_fin_ne_zero r)
  rw [Finset.mul_sum]
  refine hexp.trans (Finset.sum_congr rfl fun lam _ => ?_)
  simp only [symmetricGroupCharacter, hprod]
  ring

end

end GroundTheory.Heights₂.Heights.RestTerms
