import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

/- English proof (translation)
Introduce `E _ _ _ a b n h w m k X`. Prove the components needed by the constructor for the conclusion. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, blk_val, blk_val, dgM_val, dgMat, reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]`. Simplify using `[Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_assoc]`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, blk_val, blk_val, dgM_val, dgMat, reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]`. Establish `hk : (k.2⁻¹).val * k.2.val = 1` using `Units.inv_mul k.2`. Simplify using `[Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_assoc, hk]`.
-/
theorem blk_mul_dgM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (m k : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)),
    blk h w (k * m) X = dgM h w k * blk h w m X ∧
      blk h w (m * k) X = blk h w m (k.1.val * X * (k.2⁻¹).val) * dgM h w k := by
  intro E _ _ _ a b n h w m k X
  constructor
  · apply Units.ext
    rw [Units.val_mul, blk_val, blk_val, dgM_val, dgMat, reindex_apply, reindex_apply, reindex_apply,
      submatrix_mul_equiv, fromBlocks_multiply]
    simp [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_assoc]
  · apply Units.ext
    rw [Units.val_mul, blk_val, blk_val, dgM_val, dgMat, reindex_apply, reindex_apply, reindex_apply,
      submatrix_mul_equiv, fromBlocks_multiply]
    have hk : (k.2⁻¹).val * k.2.val = 1 := Units.inv_mul k.2
    simp [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_assoc, hk]

end GlobalTheory.BCT.CtLevel
