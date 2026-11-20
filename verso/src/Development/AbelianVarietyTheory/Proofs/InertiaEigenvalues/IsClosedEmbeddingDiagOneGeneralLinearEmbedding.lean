import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.Step.EmbClosed

/- English proof (translation)
Simplify using `[embHom, Matrix.reindex_apply, finSumFinEquiv_symm_apply_castSucc]`.
-/
theorem embHom_castSucc {r : ℕ} {k : Type} [CommRing k] (g : Matrix (Fin r) (Fin r) k) (i j : Fin r) :
    embHom r k g (Fin.castSucc i) (Fin.castSucc j) = g i j := by
  simp [embHom, Matrix.reindex_apply, finSumFinEquiv_symm_apply_castSucc]

/- English proof (translation)
Use `show Continuous fun g : Matrix (Fin r) (Fin r) F => Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 1)`. Conclude with `(Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const continuous_const).matrix_reindex _ _`.
-/
theorem continuous_embHom (r : ℕ) (F : Type) [NontriviallyNormedField F] :
    Continuous (embHom r F) := by
  show Continuous fun g : Matrix (Fin r) (Fin r) F =>
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 1)
  exact (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
    continuous_const).matrix_reindex _ _

/- English proof (translation)
The claim follows from `Function.LeftInverse.isClosedEmbedding (f := fun x : Matrix (Fin (r + 1)) (Fin (r + 1)) F => x.submatrix Fin.castSucc Fin.castSucc) (fun g => by ext i j; exact embHom_castSucc g i j) (Continuous.matrix_submatrix continuous_id _ _) (continuous_embHom r F)`.
-/
theorem isClosedEmbedding_embHom (r : ℕ) (F : Type) [NontriviallyNormedField F] :
    IsClosedEmbedding (embHom r F) :=
  Function.LeftInverse.isClosedEmbedding
    (f := fun x : Matrix (Fin (r + 1)) (Fin (r + 1)) F => x.submatrix Fin.castSucc Fin.castSucc)
    (fun g => by ext i j; exact embHom_castSucc g i j)
    (Continuous.matrix_submatrix continuous_id _ _) (continuous_embHom r F)

/- English proof (translation)
Establish `hE` using `isClosedEmbedding_embHom r F`. Set `Φ : Matrix (Fin r) (Fin r) F × (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ → Matrix (Fin (r + 1)) (Fin (r + 1)) F × (Matrix (Fin (r + 1)) (Fin (r + 1)) F)ᵐᵒᵖ` to `Prod.map (embHom r F) (MulOpposite.op ∘ embHom r F ∘ MulOpposite.unop)`. Establish `hΦ : IsClosedEmbedding Φ`. Use `hE.prodMap ?_` and prove the remaining obligations. Conclude with `MulOpposite.opHomeomorph.isClosedEmbedding.comp (hE.comp MulOpposite.opHomeomorph.symm.isClosedEmbedding)`.

Establish `hcomm : Units.embedProduct _ ∘ emb r F = Φ ∘ Units.embedProduct _`. Use function extensionality and compare the values at `g`. Both sides reduce to the same expression. Rewrite using `[← (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin (r + 1)) (Fin (r + 1)) F)).of_comp_iff, hcomm]`. Conclude with `hΦ.comp Units.isClosedEmbedding_embedProduct`.
-/
theorem isClosedEmbedding_emb (F : Type) [NontriviallyNormedField F] (r : ℕ) :
    IsClosedEmbedding (emb r F) := by
  have hE := isClosedEmbedding_embHom r F
  let Φ : Matrix (Fin r) (Fin r) F × (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ →
      Matrix (Fin (r + 1)) (Fin (r + 1)) F × (Matrix (Fin (r + 1)) (Fin (r + 1)) F)ᵐᵒᵖ :=
    Prod.map (embHom r F) (MulOpposite.op ∘ embHom r F ∘ MulOpposite.unop)
  have hΦ : IsClosedEmbedding Φ := by
    refine hE.prodMap ?_
    exact MulOpposite.opHomeomorph.isClosedEmbedding.comp
      (hE.comp MulOpposite.opHomeomorph.symm.isClosedEmbedding)
  have hcomm : Units.embedProduct _ ∘ emb r F = Φ ∘ Units.embedProduct _ := by
    funext g
    rfl
  rw [← (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin (r + 1)) (Fin (r + 1)) F)).of_comp_iff, hcomm]
  exact hΦ.comp Units.isClosedEmbedding_embedProduct

end GlobalTheory.JR.Step.EmbClosed
