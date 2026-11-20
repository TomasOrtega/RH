import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem actU_uEmb_liftH {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] {r : ℕ} (s : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (ν : E) (l : F) :
    actU (GlobalTheory.JR.Step.uEmb r E s) (GlobalTheory.JR.Step.liftH X ν l) = GlobalTheory.JR.Step.liftH (actU s X) ν l := by
  have hs : star (embHom r E s.1) = embHom r E (star s.1) := by
    simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.star_eq_conjTranspose, Matrix.reindex_apply,
      Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_one]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · apply Subtype.ext
    show embHom r E s.1 * full X.toGl * star (embHom r E s.1) = full (actU s X).toGl
    rw [hs]
    simp only [embHom, full, Hn.toGl, actU, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    congr 2
    all_goals (ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.vecMul, Finset.sum_apply, star_sum, mul_comm, Matrix.star_apply])
  · show embHom r E s.1 *ᵥ (ν • eL r E) = ν • eL r E
    ext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [embHom, eL, Matrix.mulVec, dotProduct, Matrix.reindex_apply, Fin.sum_univ_castSucc]
    · simp [embHom, eL, Matrix.mulVec, dotProduct, Matrix.reindex_apply, Fin.sum_univ_castSucc]

end GlobalTheory.JR.Step
