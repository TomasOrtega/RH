import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecZeroB

noncomputable section

open Matrix Filter Topology Set

namespace PositivityTheory.Rg.Sw.AbsSt.SZ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

/- English proof (translation)
Use `set C := (mR y).toBlocks₂₁ with hC`. Use `set D := (mR y).toBlocks₂₂ with hD`. Establish `hyG : InG (mR y)` using `y.2`. Establish `hrel : C * Dᴴ = D * Cᴴ` using `lowerDiagonalBlockAsGL hyG`. Establish `hCu : IsUnit C.det` using `isUnit_iff_ne_zero.mpr hy`.

Establish `hCHu : IsUnit (Cᴴ).det`. Rewrite using `[det_conjTranspose]`. Conclude with `isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hy)`. Use `set b := C⁻¹ * D with hb`. Establish `hbH : b.IsHermitian` using `by show bᴴ = b`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hb, conjTranspose_mul, conjTranspose_nonsing_inv]`. Use `_ = C⁻¹ * (C * Dᴴ) * (Cᴴ)⁻¹ := by`. Rewrite using `[← Matrix.mul_assoc C⁻¹, nonsing_inv_mul _ hCu, Matrix.one_mul]`. Use `_ = C⁻¹ * (D * Cᴴ) * (Cᴴ)⁻¹ := by rw [hrel]`.

Use `_ = b := by`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hCHu, Matrix.mul_one, hb]`. Take `⟨g, hg⟩` from `exists_of_InG (InG_JJ_nU hbH)`. Use `set N : M2 n := fromBlocks (-b) (-1) 1 0 with hN`. Establish `h1 : mR g⁻¹ * mR g = 1`.

Rewrite using `[← SZ.mR_mul, inv_mul_cancel]`. Both sides reduce to the same expression. Establish `h2 : mR g * N = 1`. Rewrite using `[hg, hN]`. Simplify using `only [JJ, nU, fromBlocks_multiply]`.

Rewrite using `[← fromBlocks_one]`. Apply the tactic sequence `congr 1 <;> simp`. Establish `hM : mR g⁻¹ = N`. Combine the equalities or inequalities in the displayed calculation. Use `⟨y * g⁻¹, g, b, hbH, hg, ?_, (inv_mul_cancel_right y g).symm⟩` and prove the remaining obligations.

Rewrite using `[SZ.mR_mul, hM, ← fromBlocks_toBlocks (mR y), hN, fromBlocks_multiply, toBlocks_fromBlocks₂₁]`. Rewrite using `[← hC, ← hD, Matrix.mul_neg, Matrix.mul_one, ← Matrix.mul_assoc, mul_nonsing_inv _ hCu, Matrix.one_mul, neg_add_cancel]`.
-/
lemma cell_decomp (y : GR n) (hy : ((mR y).toBlocks₂₁).det ≠ 0) :
    ∃ (p g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian ∧ mR g = JJ n * nU b ∧
      (mR p).toBlocks₂₁ = 0 ∧ y = p * g := by
  set C := (mR y).toBlocks₂₁ with hC
  set D := (mR y).toBlocks₂₂ with hD
  have hyG : InG (mR y) := y.2
  have hrel : C * Dᴴ = D * Cᴴ := lowerDiagonalBlockAsGL hyG
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.mpr hy
  have hCHu : IsUnit (Cᴴ).det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hy)
  set b := C⁻¹ * D with hb
  have hbH : b.IsHermitian := by
    show bᴴ = b
    calc bᴴ = Dᴴ * (Cᴴ)⁻¹ := by
            rw [hb, conjTranspose_mul, conjTranspose_nonsing_inv]
      _ = C⁻¹ * (C * Dᴴ) * (Cᴴ)⁻¹ := by
            rw [← Matrix.mul_assoc C⁻¹, nonsing_inv_mul _ hCu, Matrix.one_mul]
      _ = C⁻¹ * (D * Cᴴ) * (Cᴴ)⁻¹ := by rw [hrel]
      _ = b := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hCHu, Matrix.mul_one, hb]
  obtain ⟨g, hg⟩ := exists_of_InG (InG_JJ_nU hbH)
  set N : M2 n := fromBlocks (-b) (-1) 1 0 with hN
  have h1 : mR g⁻¹ * mR g = 1 := by
    rw [← SZ.mR_mul, inv_mul_cancel]
    rfl
  have h2 : mR g * N = 1 := by
    rw [hg, hN]
    simp only [JJ, nU, fromBlocks_multiply]
    rw [← fromBlocks_one]
    congr 1 <;> simp
  have hM : mR g⁻¹ = N := by
    calc mR g⁻¹ = mR g⁻¹ * (mR g * N) := by rw [h2, Matrix.mul_one]
      _ = N := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨y * g⁻¹, g, b, hbH, hg, ?_, (inv_mul_cancel_right y g).symm⟩
  rw [SZ.mR_mul, hM, ← fromBlocks_toBlocks (mR y), hN, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  rw [← hC, ← hD, Matrix.mul_neg, Matrix.mul_one, ← Matrix.mul_assoc, mul_nonsing_inv _ hCu,
    Matrix.one_mul, neg_add_cancel]

end PositivityTheory.Rg.Sw.AbsSt.SZ

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.SZ

/- English proof (translation)
Introduce `hN m n ε c t p q e sL ρ hL P`. Establish `ht : t ≠ 0`. Break down `hL.sign with ⟨h, -, -⟩ | ⟨h, -, -⟩` into its components or cases. Rewrite using `[h]`. Conclude with `hL.cpos.ne'`.

Rewrite using `[h]`. Conclude with `neg_ne_zero.2 hL.cpos.ne'`. Take `⟨C, hC, hcell⟩` from `hL.cell`. Rewrite using `[hN m n ε c t hL.cpos ht P]`. Prove the components needed by the constructor for the conclusion.

Introduce `h y`. Establish `hS : {z : GR n | ((mR z).toBlocks₂₁).det ≠ 0} ⊆ {z | sL P z = 0}`. Introduce `z hz`. Take `⟨p', g, b, hb, hg, hp, rfl⟩` from `cell_decomp z hz`. Use `show sL P (p' * g) = 0`.

Rewrite using `[hL.law P p' g hp, hcell P g b hb hg, h b hb, mul_zero, mul_zero]`. Establish `hcl : IsClosed {z : GR n | sL P z = 0}` using `isClosed_eq (hL.cont P) continuous_const`. Conclude with `hcl.closure_subset_iff.2 hS (dense_cell y)`. Introduce `h b hb`. Take `⟨g, hg⟩` from `exists_of_InG (InG_JJ_nU hb)`.

Establish `hh` using `hcell P g b hb hg`. Rewrite `hh` using `[h g]`. Conclude with `(mul_eq_zero.1 hh.symm).resolve_left hC`.
-/
theorem secZero : NullIff → SecZero := by
  intro hN m n ε c t p q e sL ρ hL P
  have ht : t ≠ 0 := by
    rcases hL.sign with ⟨h, -, -⟩ | ⟨h, -, -⟩
    · rw [h]; exact hL.cpos.ne'
    · rw [h]; exact neg_ne_zero.2 hL.cpos.ne'
  obtain ⟨C, hC, hcell⟩ := hL.cell
  rw [hN m n ε c t hL.cpos ht P]
  constructor
  · intro h y
    have hS : {z : GR n | ((mR z).toBlocks₂₁).det ≠ 0} ⊆ {z | sL P z = 0} := by
      intro z hz
      obtain ⟨p', g, b, hb, hg, hp, rfl⟩ := cell_decomp z hz
      show sL P (p' * g) = 0
      rw [hL.law P p' g hp, hcell P g b hb hg, h b hb, mul_zero, mul_zero]
    have hcl : IsClosed {z : GR n | sL P z = 0} := isClosed_eq (hL.cont P) continuous_const
    exact hcl.closure_subset_iff.2 hS (dense_cell y)
  · intro h b hb
    obtain ⟨g, hg⟩ := exists_of_InG (InG_JJ_nU hb)
    have hh := hcell P g b hb hg
    rw [h g] at hh
    exact (mul_eq_zero.1 hh.symm).resolve_left hC

end PositivityTheory.Rg.Sw.AbsSt
