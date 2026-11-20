import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedGramReEqSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedSqInverseTransposeRev
open Matrix GlobalTheory.HermFrame GlobalTheory.GradedNorm GlobalTheory.CurvInterp
open scoped ComplexOrder

namespace GlobalTheory.DualRevGraded

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem transpose_eq_map_conj {q : ℕ} {M : Matrix (Fin q) (Fin q) ℂ} (h : M.IsHermitian) :
    Mᵀ = M.map (starRingEnd ℂ) := by
  ext i j
  have := congrFun (congrFun h j) i
  simp only [conjTranspose_apply] at this
  simp [← this]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem dualRev_transpose {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ) :
    dualRev Mᵀ = (M⁻¹).submatrix Fin.rev Fin.rev := by
  simp [dualRev, GlobalTheory.HermFrame.dualGram, transpose_nonsing_inv]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem gradedGram_dualRev_re : ∀ {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ), M.PosDef → ∀ k : Fin q,
    (GlobalTheory.HermFrame.gradedGram (GlobalTheory.CurvInterp.dualRev Mᵀ) k () ()).re = (GlobalTheory.GradedNorm.grSq M (Fin.rev k))⁻¹ := by
  intro q M hM k
  have hN : (dualRev Mᵀ).PosDef := by
    rw [dualRev_transpose]; exact PosDef.submatrix hM.inv Fin.rev_injective
  rw [GlobalTheory.GradedGramRe.gradedGram_re_eq_grSq _ hN k, dualRev_transpose]
  have h := GlobalTheory.grSq_inv_transpose_rev Mᵀ hM.transpose (Fin.rev k)
  rw [Fin.rev_rev, transpose_nonsing_inv, transpose_transpose, transpose_eq_map_conj hM.1, grSq_map_conj] at h
  exact h

end GlobalTheory.DualRevGraded
