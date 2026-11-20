import ReciprocityTheory.DualLattices.IsotypicAveragingStatement
import ReciprocityTheory.DualLattices.ThmAUses

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

/- English proof (translation)
Simplify using `[stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Finset.sum_sub_distrib, sub_eq_add_neg, add_comm]`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_neg_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma stdJ_form' {D : Type} [CommRing D] {g : ℕ}
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (i j : Fin g ⊕ Fin g) :
    (Mᵀ * stdJ D g * M) i j =
      ∑ a, (M (Sum.inr a) i * M (Sum.inl a) j - M (Sum.inl a) i * M (Sum.inr a) j) := by
  simp [stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Finset.sum_sub_distrib,
    sub_eq_add_neg, add_comm]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

/- English proof (translation)
Rewrite using `[stdJ]`. Simplify using `[Matrix.fromBlocks_multiply]`.
-/
private lemma stdJ_eq (D : Type) [CommRing D] (g : ℕ) :
    stdJ D g = fromBlocks 1 (-1) 0 1 * fromBlocks 1 0 1 1 * fromBlocks 1 (-1) 0 1 := by
  rw [stdJ]
  simp [Matrix.fromBlocks_multiply]

/- English proof (translation)
Rewrite using `[stdJ_eq, Matrix.det_mul, Matrix.det_mul]`. Simplify using `[Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂]`.
-/
private lemma det_stdJ (D : Type) [CommRing D] (g : ℕ) : (stdJ D g).det = 1 := by
  rw [stdJ_eq, Matrix.det_mul, Matrix.det_mul]
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂]

/- English proof (translation)
Introduce `S _ g m Ht Bt E cp εT εL π hπ hT hT1 hL hL1 hHt hE hBH`. Introduce `Bt'`. Establish `hBt' : Bt' = ∑ i, εL i * Bt * εT i` using `rfl`. Establish `hLt : ∀ i, (εL i)ᵀ * Ht = Ht * εT (π i)`. Introduce `i`.

Establish `h` using `hHt (π i)`. Rewrite `h` using `[hπ]`. Conclude with `h.symm`. Establish `hHtL : ∀ i, Htᵀ * εL i = (εT (π i))ᵀ * Htᵀ`. Introduce `i`.

Establish `h` using `congrArg Matrix.transpose (hLt i)`. Simplify `h` using `[Matrix.transpose_mul]`. Establish `part2 : ∀ i, Bt' * εT i = εL i * Bt'`. Introduce `i`. Establish `l : ∀ j, εL j * Bt * εT j * εT i = if j = i then εL j * Bt * εT j else 0`.

Introduce `j`. Rewrite using `[Matrix.mul_assoc (εL j * Bt), hT j i]`. Use `split_ifs with h`. Substitute `h` using the available equality. Both sides reduce to the same expression.

Simplify using the standard rewrite rules. Establish `r : ∀ j, εL i * (εL j * Bt * εT j) = if j = i then εL j * Bt * εT j else 0`. Introduce `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Rewrite using `[if_pos rfl, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, if_pos rfl]`. Rewrite using `[if_neg h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, if_neg (Ne.symm h), Matrix.zero_mul, Matrix.zero_mul]`. Rewrite using `[hBt', Matrix.sum_mul, Matrix.mul_sum]`. Simplify using `only [l, r]`. Establish `hA : Bt'ᵀ * Ht = ∑ i, (εT i)ᵀ * Btᵀ * Ht * εT (π i)`.

Rewrite using `[hBt', Matrix.transpose_sum, Matrix.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hLt i]`.

Establish `hB : Htᵀ * Bt' = ∑ i, (εT i)ᵀ * Htᵀ * Bt * εT (π i)`. Rewrite using `[hBt', Matrix.mul_sum, ← Equiv.sum_comp π (fun i => Htᵀ * (εL i * Bt * εT i))]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[hHtL (π i), hπ]`.

Establish `part1 : Bt'ᵀ * Ht - Htᵀ * Bt' = cp • E`. Rewrite using `[hA, hB, ← Finset.sum_sub_distrib]`. Establish `h : ∀ i, (εT i)ᵀ * Btᵀ * Ht * εT (π i) - (εT i)ᵀ * Htᵀ * Bt * εT (π i) = cp • (E * εT (π i))`. Introduce `i`. Rewrite using `[Matrix.mul_assoc ((εT i)ᵀ) Btᵀ Ht, Matrix.mul_assoc ((εT i)ᵀ) Htᵀ Bt, ← Matrix.sub_mul, ← Matrix.mul_sub, hBH, Matrix.mul_smul, hE i, Matrix.smul_mul, Matrix.mul_assoc, hT, if_pos rfl]`.

Simplify using `only [h]`. Rewrite using `[← Finset.smul_sum, ← Matrix.mul_sum, Equiv.sum_comp π εT, hT1, Matrix.mul_one]`. Establish `hJ : (Matrix.fromRows Ht Bt')ᵀ * stdJ S g * Matrix.fromRows Ht Bt' = cp • E`. Rewrite using `[← part1]`. Use extensionality with `i j`.

Rewrite using `[stdJ_form']`. Simplify using `[Matrix.sub_apply, Matrix.mul_apply, Finset.sum_sub_distrib]`. Use `⟨part1, part2, ?_⟩` and prove the remaining obligations. Rewrite using `[det_sq_eq E _ cp hJ, det_stdJ, mul_one]`.
-/
theorem u1 : IsotypicAveragingStatement := by
  intro S _ g m Ht Bt E cp εT εL π hπ hT hT1 hL hL1 hHt hE hBH
  intro Bt'
  have hBt' : Bt' = ∑ i, εL i * Bt * εT i := rfl
  have hLt : ∀ i, (εL i)ᵀ * Ht = Ht * εT (π i) := by
    intro i
    have h := hHt (π i)
    rw [hπ] at h
    exact h.symm
  have hHtL : ∀ i, Htᵀ * εL i = (εT (π i))ᵀ * Htᵀ := by
    intro i
    have h := congrArg Matrix.transpose (hLt i)
    simpa [Matrix.transpose_mul] using h
  have part2 : ∀ i, Bt' * εT i = εL i * Bt' := by
    intro i
    have l : ∀ j, εL j * Bt * εT j * εT i = if j = i then εL j * Bt * εT j else 0 := by
      intro j
      rw [Matrix.mul_assoc (εL j * Bt), hT j i]
      split_ifs with h
      · subst h; rfl
      · simp
    have r : ∀ j, εL i * (εL j * Bt * εT j) = if j = i then εL j * Bt * εT j else 0 := by
      intro j
      by_cases h : j = i
      · subst h
        rw [if_pos rfl, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, if_pos rfl]
      · rw [if_neg h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, if_neg (Ne.symm h),
          Matrix.zero_mul, Matrix.zero_mul]
    rw [hBt', Matrix.sum_mul, Matrix.mul_sum]
    simp only [l, r]
  have hA : Bt'ᵀ * Ht = ∑ i, (εT i)ᵀ * Btᵀ * Ht * εT (π i) := by
    rw [hBt', Matrix.transpose_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [hLt i]
  have hB : Htᵀ * Bt' = ∑ i, (εT i)ᵀ * Htᵀ * Bt * εT (π i) := by
    rw [hBt', Matrix.mul_sum, ← Equiv.sum_comp π (fun i => Htᵀ * (εL i * Bt * εT i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [← Matrix.mul_assoc]
    rw [hHtL (π i), hπ]
  have part1 : Bt'ᵀ * Ht - Htᵀ * Bt' = cp • E := by
    rw [hA, hB, ← Finset.sum_sub_distrib]
    have h : ∀ i, (εT i)ᵀ * Btᵀ * Ht * εT (π i) - (εT i)ᵀ * Htᵀ * Bt * εT (π i) =
        cp • (E * εT (π i)) := by
      intro i
      rw [Matrix.mul_assoc ((εT i)ᵀ) Btᵀ Ht, Matrix.mul_assoc ((εT i)ᵀ) Htᵀ Bt, ← Matrix.sub_mul,
        ← Matrix.mul_sub, hBH, Matrix.mul_smul, hE i, Matrix.smul_mul, Matrix.mul_assoc, hT,
        if_pos rfl]
    simp only [h]
    rw [← Finset.smul_sum, ← Matrix.mul_sum, Equiv.sum_comp π εT, hT1, Matrix.mul_one]
  have hJ : (Matrix.fromRows Ht Bt')ᵀ * stdJ S g * Matrix.fromRows Ht Bt' = cp • E := by
    rw [← part1]
    ext i j
    rw [stdJ_form']
    simp [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_sub_distrib]
  refine ⟨part1, part2, ?_⟩
  rw [det_sq_eq E _ cp hJ, det_stdJ, mul_one]

end ReciprocityTheory.PGsh.Up
