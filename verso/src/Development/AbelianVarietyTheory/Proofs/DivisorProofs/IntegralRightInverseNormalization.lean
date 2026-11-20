import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open ValuativeRel Matrix

namespace GlobalTheory

/- English proof (translation)
Establish `key : (Y * Q').det = ∑ p : Fin s → D, (∏ i, Q' (p i) i) * (Y.submatrix id p).det`. Simplify using `only [det_apply', mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ, submatrix_apply, id]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[hYQ, det_one]`. Take `⟨p₀, -, hp₀⟩` from `Finset.exists_ne_zero_of_sum_ne_zero (key ▸ one_ne_zero)`. Use `haveI : Nonempty (Fin s → D) := ⟨p₀⟩`. Take `⟨κ, hκ⟩` from `Finite.exists_max (fun p : Fin s → D => valuation k (Y.submatrix id p).det)`.

Establish `hne : (Y.submatrix id κ).det ≠ 0`. Introduce `h0`. Use `hκ p₀` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `right_ne_zero_of_mul hp₀ ((valuation k).zero_iff.mp (le_antisymm this zero_le'))`.

Use `set h := (Y.submatrix id κ)⁻¹ with hh`. Establish `hsub : ∀ p : Fin s → D, (h * Y).submatrix id p = h * Y.submatrix id p`. Introduce `p`. Use extensionality with `r c`. Simplify using `[mul_apply]`.

Establish `hone : (h * Y).submatrix id κ = 1`. Rewrite using `[hsub, hh]`. Conclude with `nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hne)`. Use `⟨h, Matrix.of fun j l => if j = κ l then 1 else 0, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`.

Establish `e : (h * Y) i j = ((h * Y).submatrix id (Function.update κ i j)).det`. Establish `: (h * Y).submatrix id (Function.update κ i j) = (1 : Matrix (Fin s) (Fin s) k).updateCol i (fun r => (h * Y) r j)`. Use extensionality with `r c`. Distinguish the cases in `hc : c = i`. Substitute `hc` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[updateCol_ne hc, ← hone]`. Simplify using `[Function.update_of_ne hc]`. Rewrite using `[this, ← cramer_apply, cramer_one]`. Both sides reduce to the same expression.

Rewrite using `[Valuation.mem_integer_iff, e, hsub, det_mul, hh, det_nonsing_inv, Ring.inverse_eq_inv', map_mul, map_inv₀]`. Establish `hpos : 0 < valuation k (Y.submatrix id κ).det` using `lt_of_le_of_ne zero_le' (Ne.symm ((valuation k).ne_zero_iff.mpr hne))`. Rewrite using `[mul_comm, ← div_eq_mul_inv, div_le_one₀ hpos]`. Conclude with `hκ _`. Introduce `i j`.

Rewrite using `[Matrix.of_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Establish `: h * Y * (Matrix.of fun j l => if j = κ l then (1 : k) else 0 : Matrix D (Fin s) k) = (h * Y).submatrix id κ`.

Use extensionality with `r l`. Simplify using `[mul_apply]`. Rewrite using `[this, hone]`.
-/
theorem frame_normalise_integral (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (s : ℕ)
    (Y : Matrix (Fin s) D k) (Q' : Matrix D (Fin s) k) (hYQ : Y * Q' = 1) :
    ∃ (h : Matrix (Fin s) (Fin s) k) (Q : Matrix D (Fin s) k),
      (∀ i j, (h * Y) i j ∈ 𝒪[k]) ∧ (∀ i j, Q i j ∈ 𝒪[k]) ∧ h * Y * Q = 1 := by
  classical

  have key : (Y * Q').det = ∑ p : Fin s → D, (∏ i, Q' (p i) i) * (Y.submatrix id p).det := by
    simp only [det_apply', mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ,
      submatrix_apply, id]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib]; ring
  rw [hYQ, det_one] at key
  obtain ⟨p₀, -, hp₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (key ▸ one_ne_zero)
  haveI : Nonempty (Fin s → D) := ⟨p₀⟩
  obtain ⟨κ, hκ⟩ := Finite.exists_max (fun p : Fin s → D => valuation k (Y.submatrix id p).det)
  have hne : (Y.submatrix id κ).det ≠ 0 := by
    intro h0
    have := hκ p₀
    rw [h0, map_zero] at this
    exact right_ne_zero_of_mul hp₀ ((valuation k).zero_iff.mp (le_antisymm this zero_le'))
  set h := (Y.submatrix id κ)⁻¹ with hh
  have hsub : ∀ p : Fin s → D, (h * Y).submatrix id p = h * Y.submatrix id p := by
    intro p; ext r c; simp [mul_apply]
  have hone : (h * Y).submatrix id κ = 1 := by
    rw [hsub, hh]
    exact nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hne)
  refine ⟨h, Matrix.of fun j l => if j = κ l then 1 else 0, ?_, ?_, ?_⟩
  · intro i j
    have e : (h * Y) i j = ((h * Y).submatrix id (Function.update κ i j)).det := by
      have : (h * Y).submatrix id (Function.update κ i j) =
          (1 : Matrix (Fin s) (Fin s) k).updateCol i (fun r => (h * Y) r j) := by
        ext r c
        by_cases hc : c = i
        · subst hc; simp
        · rw [updateCol_ne hc, ← hone]
          simp [Function.update_of_ne hc]
      rw [this, ← cramer_apply, cramer_one]; rfl
    rw [Valuation.mem_integer_iff, e, hsub, det_mul, hh, det_nonsing_inv, Ring.inverse_eq_inv',
      map_mul, map_inv₀]
    have hpos : 0 < valuation k (Y.submatrix id κ).det :=
      lt_of_le_of_ne zero_le' (Ne.symm ((valuation k).ne_zero_iff.mpr hne))
    rw [mul_comm, ← div_eq_mul_inv, div_le_one₀ hpos]
    exact hκ _
  · intro i j
    rw [Matrix.of_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · have : h * Y * (Matrix.of fun j l => if j = κ l then (1 : k) else 0 : Matrix D (Fin s) k) =
        (h * Y).submatrix id κ := by
      ext r l; simp [mul_apply]
    rw [this, hone]

end GlobalTheory
