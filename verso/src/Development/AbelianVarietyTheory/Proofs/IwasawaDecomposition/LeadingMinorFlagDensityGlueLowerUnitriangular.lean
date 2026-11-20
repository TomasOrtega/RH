import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorBlockDecompositionStatement

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

variable {r p q : ℕ}

/- English proof (translation)
Use `conv_lhs => rw [← fromBlocks_toBlocks S]`. Simplify using `[fromBlocks_conjTranspose, fromBlocks_multiply]`.
-/
theorem blockDiag_conj (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (a : Matrix (Fin p) (Fin p) ℂ)
    (b : Matrix (Fin q) (Fin q) ℂ) :
    (fromBlocks a 0 0 b)ᴴ * S * fromBlocks a 0 0 b =
      fromBlocks (aᴴ * S.toBlocks₁₁ * a) (aᴴ * S.toBlocks₁₂ * b) (bᴴ * S.toBlocks₂₁ * a) (bᴴ * S.toBlocks₂₂ * b) := by
  conv_lhs => rw [← fromBlocks_toBlocks S]
  simp [fromBlocks_conjTranspose, fromBlocks_multiply]

/- English proof (translation)
Establish `hb' : IsUnit bᴴ.det` using `by rw [det_conjTranspose]; exact hb.star`. Rewrite using `[blockDiag_conj, schur, schur]`. Simplify using `only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]`. Rewrite using `[mul_nonsing_inv_cancel_left _ _ hb, nonsing_inv_mul_cancel_left _ _ hb']`.
-/
theorem schur_blockDiag_conj (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (a : Matrix (Fin p) (Fin p) ℂ)
    {b : Matrix (Fin q) (Fin q) ℂ} (hb : IsUnit b.det) :
    schur ((fromBlocks a 0 0 b)ᴴ * S * fromBlocks a 0 0 b) = aᴴ * schur S * a := by
  have hb' : IsUnit bᴴ.det := by rw [det_conjTranspose]; exact hb.star
  rw [blockDiag_conj, schur, schur]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
  rw [mul_nonsing_inv_cancel_left _ _ hb, nonsing_inv_mul_cancel_left _ _ hb']

/- English proof (translation)
Establish `h1 : reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) = (reindex e e (uni (glue e w)))ᴴ * reindex e e A * reindex e e (uni (glue e w))`. Simplify using `only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]`. Establish `h2 : fromBlocks (uni w.2.2) (toMat w.1 * uni w.2.1) 0 (uni w.2.1) = (fromBlocks 1 (toMat w.1) 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * fromBlocks (uni w.2.2) 0 0 (uni w.2.1)`. Simplify using `[fromBlocks_multiply]`. Rewrite using `[h1, reindex_uni_glue he, h2, shear]`.

Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`.
-/
theorem reindex_conj_glue {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) (A : Matrix (Fin r) (Fin r) ℂ)
    (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)) :
    reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) =
      (fromBlocks (uni w.2.2) 0 0 (uni w.2.1))ᴴ * shear (reindex e e A) (toMat w.1) *
        fromBlocks (uni w.2.2) 0 0 (uni w.2.1) := by
  have h1 : reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) =
      (reindex e e (uni (glue e w)))ᴴ * reindex e e A * reindex e e (uni (glue e w)) := by
    simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
  have h2 : fromBlocks (uni w.2.2) (toMat w.1 * uni w.2.1) 0 (uni w.2.1) =
      (fromBlocks 1 (toMat w.1) 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *
        fromBlocks (uni w.2.2) 0 0 (uni w.2.1) := by
    simp [fromBlocks_multiply]
  rw [h1, reindex_uni_glue he, h2, shear]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

/- English proof (translation)
Introduce `r p q e he A w hS`. Establish `hR` using `reindex_conj_glue he A w`. Use `set S := shear (reindex e e A) (toMat w.1) with hSdef`. Use `set H := (uni (glue e w))ᴴ * A * uni (glue e w) with hH`. Establish `h22 : (reindex e e H).toBlocks₂₂ = (uni w.2.1)ᴴ * S.toBlocks₂₂ * uni w.2.1`.

Rewrite using `[hR, blockDiag_conj, toBlocks_fromBlocks₂₂]`. Establish `hd : (reindex e e H).toBlocks₂₂.det = S.toBlocks₂₂.det`. Rewrite using `[h22, det_mul, det_mul, det_conjTranspose, det_uni]`. Simplify using the standard rewrite rules. Establish `hs : schur (reindex e e H) = (uni w.2.2)ᴴ * schur S * uni w.2.2`.

Rewrite using `[hR, schur_blockDiag_conj _ _ (by rw [det_uni]; exact isUnit_one)]`. Take `⟨m1, m2⟩` from `GlobalTheory.T.leadingMinor_blockDecomposition r p q e he H (hd ▸ hS)`. Rewrite `m2` using `[hd, hs]`. Rewrite `m1` using `[h22]`. Unfold `dens`.

Rewrite using `[← hH, ← Equiv.prod_comp e.symm, Fintype.prod_sum_type]`. Establish `a1 : ∀ a : Fin q, lminor H (e.symm (Sum.inr a)).castSucc = lminor ((uni w.2.1)ᴴ * S.toBlocks₂₂ * uni w.2.1) a.castSucc` using `fun a => m1 _ _ (by simp [he.2])`. Establish `a2 : ∀ a : Fin p, lminor H (e.symm (Sum.inl a)).castSucc = S.toBlocks₂₂.det * lminor ((uni w.2.2)ᴴ * schur S * uni w.2.2) a.castSucc` using `fun a => m2 _ _ (by simp [he.1])`. Simplify using `only [a1, a2, norm_mul, mul_zpow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[← zpow_natCast, ← _root_.zpow_mul, neg_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dens_glue : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ) (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)), IsUnit (shear (reindex e e A) (toMat w.1)).toBlocks₂₂.det → dens A (glue e w) = dens (shear (reindex e e A) (toMat w.1)).toBlocks₂₂ w.2.1 * ‖(shear (reindex e e A) (toMat w.1)).toBlocks₂₂.det‖ ^ (-(2 * p : ℤ)) * dens (schur (shear (reindex e e A) (toMat w.1))) w.2.2 := by
  intro r p q e he A w hS
  have hR := reindex_conj_glue he A w
  set S := shear (reindex e e A) (toMat w.1) with hSdef
  set H := (uni (glue e w))ᴴ * A * uni (glue e w) with hH
  have h22 : (reindex e e H).toBlocks₂₂ = (uni w.2.1)ᴴ * S.toBlocks₂₂ * uni w.2.1 := by
    rw [hR, blockDiag_conj, toBlocks_fromBlocks₂₂]
  have hd : (reindex e e H).toBlocks₂₂.det = S.toBlocks₂₂.det := by
    rw [h22, det_mul, det_mul, det_conjTranspose, det_uni]; simp
  have hs : schur (reindex e e H) = (uni w.2.2)ᴴ * schur S * uni w.2.2 := by
    rw [hR, schur_blockDiag_conj _ _ (by rw [det_uni]; exact isUnit_one)]
  obtain ⟨m1, m2⟩ := GlobalTheory.T.leadingMinor_blockDecomposition r p q e he H (hd ▸ hS)
  rw [hd, hs] at m2
  rw [h22] at m1
  unfold dens
  rw [← hH, ← Equiv.prod_comp e.symm, Fintype.prod_sum_type]
  have a1 : ∀ a : Fin q, lminor H (e.symm (Sum.inr a)).castSucc =
      lminor ((uni w.2.1)ᴴ * S.toBlocks₂₂ * uni w.2.1) a.castSucc := fun a => m1 _ _ (by simp [he.2])
  have a2 : ∀ a : Fin p, lminor H (e.symm (Sum.inl a)).castSucc =
      S.toBlocks₂₂.det * lminor ((uni w.2.2)ᴴ * schur S * uni w.2.2) a.castSucc := fun a => m2 _ _ (by simp [he.1])
  simp only [a1, a2, norm_mul, mul_zpow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← zpow_natCast, ← _root_.zpow_mul, neg_mul]
  ring

end GlobalTheory.FlagFibre
